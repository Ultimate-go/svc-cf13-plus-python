"""VDS 会话 —— 把 :mod:`svc`、:mod:`vds.storage_node`、:mod:`vds.client_node` 串成一条可跑的流水线。

论文 §8.2 的 ``VDS2`` 是把 §5.2 的 SVC 套上「一个客户端 + 多个存储节点」的框架。
本模块提供 ``VDSSession``，它扮演「公开参数 + 全局状态」的角色，
把各算法需要的 ``pp``、:math:`U_n`、:math:`e_{[n]}` 集中管起来。

主流程（对应图片里那段需求）
----------------------------
::

    1. 客户端把文件切成 n 块          →  VDSSession.commit_file(blocks)
    2. 分发给若干存储节点              →  VDSSession.distribute(...)
    3. 任何人检索其中若干部分          →  StorageNode.retrieve(Q)
    4. 把多份证据聚合成一个证据        →  ClientNode.aggregate_certificates(certs)
    5. 客户端验证这一个证据            →  ClientNode.ver_retrieve(Q, F_Q, pi_K)

第 4 步就是论文的 ``AggregateCertificates``，第 5 步是 ``ClntNode.VerRetrieve``。
"""

from __future__ import annotations

from typing import Iterable, Sequence

from svc import (
    CRS,
    CRSn,
    DeterministicRNG,
    Opening,
    PrimeGen,
    commit as svc_commit,
    open_subvector,
    product_tree,
    setup as svc_setup,
    specialize as svc_specialize,
)
from svc.types import as_index_set

from .client_node import Certificate, ClientNode
from .digest import Digest, LocalView
from .encoding import blocks_for_length, split_bytes
from .storage_node import StorageNode

__all__ = ["VDSSession"]


class VDSSession:
    """一次 VDS 会话：持有公开参数 ``pp``，并缓存各 ``n`` 下的 ``crs_n``。

    :param n_max: 文件最多分成多少块（同时也是素数映射的容量）。
                  **这个值在会话期间不可变**，因为素数 ``e_1..e_{n_max}``
                  必须固定 —— 摘要里的 :math:`U`、:math:`C` 都建立在它们之上。
    :param l: 每个块的比特数。取 ``8 * 每块字节数``。
    :param lambda_bits: 安全参数 :math:`\\lambda`
    :param modulus_bits: 模数位长，``None`` 时取 ``16·λ``
    :param seed: 随机种子（可复现）

    .. note::

       ``n_max`` 必须**事先定死**，这是本方案（以及所有基于隐藏阶群的
       累加器方案）的结构性约束：素数一旦选定，``U`` 就绑死了，
       事后无法凭空增加可用位置。所以 ``Bootstrap`` 阶段就要给出上限，
       文件长度在这个上限内可以任意增删。
    """

    def __init__(
        self,
        n_max: int,
        l: int = 128,
        lambda_bits: int = 128,
        modulus_bits: int | None = None,
        seed: bytes | str = b"vds-v2",
        primegen_cls: type = PrimeGen,
    ) -> None:
        self.n_max = n_max
        self.l = l
        self.rng = DeterministicRNG(seed)

        # pp = (G, g, PrimeGen, l)；n_max 个位置一次性备好素数映射
        self.crs: CRS = svc_setup(
            lambda_bits=lambda_bits,
            l=l,
            n=n_max,
            rng=self.rng,
            modulus_bits=modulus_bits,
            primegen_cls=primegen_cls,
        )

        # n -> CRSn 的缓存。同一个 n 的 e_all 只算一次。
        self._crsn_cache: dict[int, CRSn] = {}
        # 承诺时算出来的 S_i 列表也缓存一下（commit / open 都要用）
        self._e_all_cache: dict[int, int] = {}

    # -------------------------------------------------------------------
    # Bootstrap
    # -------------------------------------------------------------------

    def bootstrap(self) -> Digest:
        """``Bootstrap(1λ, ℓ) → (pp, δ0, n0, st0)``。

        论文原文：``Set n0 ← 0, δ0 ← ((1, g), n0) and st0 ← g``。

        注意 ``δ0`` 里的 :math:`U = 1`、:math:`C = g` 是**空文件**的约定取值，
        只用于「文件还没建立」这个初始状态；真正的文件摘要由
        :meth:`commit_file` 产出。
        """
        return Digest(U=1, C=self.crs.g, n=0)

    # -------------------------------------------------------------------
    # crs_n 缓存
    # -------------------------------------------------------------------

    def e_all_for(self, n: int) -> int:
        """:math:`e_{[n]} = \\prod_{i=1}^{n} e_i`，带缓存。"""
        if n not in self._e_all_cache:
            self._e_all_cache[n] = product_tree(self.crs.primegen.first(n))
        return self._e_all_cache[n]

    def crs_n_for(self, delta: Digest) -> CRSn:
        """由摘要取出与它匹配的 :class:`~svc.CRSn`。

        :math:`e_{[n]}` 由 ``n`` 唯一决定（素数映射固定），
        :math:`U_n` 则直接取摘要里的值 —— 这正是论文把 ``U`` 挂进摘要的好处：
        验证方不需要自己重算 :math:`g^{e_{[n]}}`（那要一次巨大的模幂）。
        """
        n = delta.n
        if n <= 0:
            raise ValueError("空文件（n=0）没有 crs_n；请先 commit_file")
        cached = self._crsn_cache.get(n)
        if cached is None or cached.U_n != delta.U:
            cached = CRSn(
                crs=self.crs, U_n=delta.U, e_all=self.e_all_for(n), n=n
            )
            self._crsn_cache[n] = cached
        return cached

    # -------------------------------------------------------------------
    # 建立文件
    # -------------------------------------------------------------------

    def commit_file(
        self,
        values: Sequence[int],
        progress=None,
    ) -> tuple[Digest, CRSn]:
        """把向量 ``values`` 变成一个文件：``VC.Specialize`` + ``VC.Com``。

        :param progress: 可选的进度回调 ``progress(done, total, detail)``。
                         长任务（几千块）下最难等的是素数生成那一段，
                         回调让调用方能报告进度。默认为 ``None``，行为不变。
        :returns: ``(摘要, crs_n)``。``crs_n`` 交还给调用方是为了后续
                  :func:`svc.open_subvector` / :func:`svc.disagg` 复用，
                  免得重复算 ``e_all``。
        """
        n = len(values)
        if n == 0:
            raise ValueError("空文件没有意义；至少要有 1 块")
        if n > self.n_max:
            raise ValueError(
                f"文件 {n} 块超过了会话上限 n_max = {self.n_max}。"
                f"隐藏阶群方案的可用位置在 Bootstrap 阶段就定死了，无法事后扩。"
            )
        for v in values:
            if v < 0 or v >= (1 << self.l):
                raise ValueError(f"值 {v} 超出 l = {self.l} 位的范围 [0, 2^{self.l})")

        total = 3
        if progress is not None:
            progress(0, total, f"生成 {n} 个素数并累加出 U_n")
        crs_n = svc_specialize(self.crs, n)

        if progress is not None:
            progress(1, total, "计算承诺 C")
        com = svc_commit(crs_n, values)

        delta = Digest(U=crs_n.U_n, C=com.C, n=n)
        self._crsn_cache[n] = crs_n
        if progress is not None:
            progress(total, total, "完成")
        return delta, crs_n

    def commit_bytes(
        self, data: bytes, block_bytes: int, progress=None
    ) -> tuple[Digest, CRSn, tuple[int, ...], int]:
        """``bytes`` 版本的便捷入口。

        :returns: ``(摘要, crs_n, 向量, 原始字节长度)``
        """
        if block_bytes * 8 != self.l:
            raise ValueError(
                f"block_bytes={block_bytes} 与 l={self.l} 不匹配"
                f"（要求 l = 8·block_bytes）"
            )
        values = split_bytes(data, block_bytes)
        delta, crs_n = self.commit_file(values, progress=progress)
        return delta, crs_n, tuple(values), len(data)

    # -------------------------------------------------------------------
    # 分发
    # -------------------------------------------------------------------

    def distribute(
        self,
        delta: Digest,
        values: Sequence[int],
        assignments: Iterable[Sequence[int]],
        crs_n: CRSn | None = None,
        progress=None,
    ) -> list[StorageNode]:
        """把文件按 ``assignments`` 分发给若干存储节点。

        每个节点拿到的证据都是**独立生成**的子向量打开证明
        :math:`\\pi_I`（不是从别处拆的），因为分发发生在文件刚建立时。
        后续节点之间要合并/拆分走 :meth:`StorageNode.add_storage` /
        :meth:`StorageNode.rmv_storage`。

        :param assignments: 若干组下标；各组**必须两两不相交**，
                            否则同一个下标会被两个节点各自声称持有，
                            后面聚合时 :func:`svc.agg` 会因交集非空而报错。
        """
        crs_n = crs_n or self.crs_n_for(delta)
        values = list(values)

        groups = list(assignments)
        total = len(groups)
        seen: set[int] = set()
        nodes: list[StorageNode] = []
        for idx, raw in enumerate(groups):
            I_set = as_index_set(raw)
            if not I_set:
                continue
            overlap = seen & set(I_set)
            if overlap:
                raise ValueError(
                    f"第 {idx} 组与前面的分配重叠于 {sorted(overlap)}；"
                    f"同一块数据只能有一个负责人"
                )
            if I_set[-1] >= len(values):
                raise ValueError(f"第 {idx} 组含越界下标 {I_set[-1]}")
            seen |= set(I_set)

            pi_I = open_subvector(
                crs_n, I_set, [values[i] for i in I_set], values
            )
            nodes.append(
                StorageNode(
                    node_id=f"node-{idx}",
                    session=self,
                    view=LocalView(
                        delta=delta,
                        st=pi_I,
                        I=I_set,
                        FI=tuple(values[i] for i in I_set),
                    ),
                )
            )
            if progress is not None:
                progress(idx + 1, total, f"node-{idx} 拿到 {len(I_set)} 块的证明")
        return nodes

    # -------------------------------------------------------------------
    # 便捷端点
    # -------------------------------------------------------------------

    def make_client(self, delta: Digest) -> ClientNode:
        """造一个只持有摘要的客户端。"""
        return ClientNode(self, delta)

    def retrieve_from(
        self,
        nodes: Sequence[StorageNode],
        Q: Sequence[int],
    ) -> tuple[tuple[int, ...], list[Certificate], list[str]]:
        """向覆盖 ``Q`` 的节点们发起检索，收集凭证。

        这是「任何人都可以检索」这句需求的落地点：调用方不需要知道
        ``Q`` 具体落在哪个节点上，本方法会自己挑出能覆盖它的节点组合。

        :returns: ``(F_Q, 凭证列表, 参与节点名)``

        :raises ValueError: 没有任何单个节点能覆盖 ``Q``。
                            真实系统里应当把 ``Q`` 再切细，
                            或先让节点之间做 :meth:`StorageNode.add_storage`。
        """
        Q_set = as_index_set(Q)
        remaining = set(Q_set)
        certs: list[Certificate] = []
        used: list[str] = []

        for node in nodes:
            if not remaining:
                break
            take = sorted(remaining & set(node.I))
            if not take:
                continue
            F_part, pi_part = node.retrieve(take)
            certs.append(Certificate(take, F_part, pi_part, node.node_id))
            used.append(node.node_id)
            remaining -= set(take)

        if remaining:
            raise ValueError(
                f"没有节点覆盖下标 {sorted(remaining)}；"
                f"请让节点间先做 AddStorage 合并，或换一组检索目标"
            )

        valmap: dict[int, int] = {}
        for c in certs:
            valmap.update(dict(zip(c.Q, c.F_Q)))
        return tuple(valmap[i] for i in Q_set), certs, used

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"VDSSession(n_max={self.n_max}, l={self.l}, "
            f"N={self.crs.N.bit_length()}位, 素数已算={self.crs.primegen.computed})"
        )
