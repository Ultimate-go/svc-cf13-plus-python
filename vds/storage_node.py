"""存储节点 —— 论文 §7 的 ``StrgNode`` 算法族。

本模块实现与「检索 + 聚合 + 验证」这条主流程直接相关的算法：

======================  ====================================================
论文算法                 本模块
======================  ====================================================
``StrgNode.AddStorage``  :meth:`StorageNode.add_storage` —— 合并另一份存储
                                                         或**一份检索凭证**
``StrgNode.RmvStorage``  :meth:`StorageNode.rmv_storage` —— 删掉一部分存储
``StrgNode.Retrieve``    :meth:`StorageNode.retrieve` —— 返回内容 + 证据
``StrgNode.CreateFrom``  :meth:`StorageNode.create_from` —— 从大文件里派生子文件
======================  ====================================================

「证据」到底是谁
----------------
节点返回的 :math:`\\pi_Q` **不是**重新算了一遍 :math:`\\Lambda_Q`，
而是用 **disaggregation** 从它手里的 :math:`\\pi_I` 直接拆出来的：

.. math::
    \\pi_Q \\leftarrow VC.\\text{Disagg}(pp, I, F_I, \\pi_I, Q), \\qquad Q \\subseteq I

这一点是本方案相比朴素做法最省的地方：节点**不需要**保存原始文件之外的
任何东西，也不需要为每个可能的 ``Q`` 预先算证明；一次拆分的代价只与
``|I \\setminus Q|`` 有关。论文原文：
``Compute both portion FQ ⊆ FI as well as proof πQ ← VC.Disagg′(pp, I, FI, st, Q)``。
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Sequence

from svc import (
    CRSn,
    Opening,
    agg,
    disagg,
    e_of,
    verify as svc_verify,
)
from svc.types import as_index_set

from .digest import Digest, LocalView

if TYPE_CHECKING:  # pragma: no cover
    from .pos import PoSProof
    from .vds import VDSSession

__all__ = ["StorageNode", "UpdateWitness", "UpdateDelta"]


class UpdateWitness:
    """``Υ∆`` —— 更新见证，充当「更新密钥」。

    论文对三种 ``op`` 给的形态不同（``mod`` / ``del`` 是 ``(F_K, S_K)``，
    ``add`` 只是 ``S_K``），这里统一成「一个群元素 + ``K`` 上的值 + 可选的 ``π_K``」。

    :param S_K: 更新密钥。``mod`` / ``del`` 取 :math:`g^{e_{[n]}/e_K}`，
                一个群元素就够对方推出整批 :math:`S_i`（见 :func:`_membership_witnesses`）。
                ``add`` 取**旧的累加器** :math:`U` —— 新位置在旧文件里没有成员见证，
                而 :math:`g^{e_{[n']}/e_K} = g^{e_{[n]}}` 恰好就是 :math:`U`。
    :param F_K: ``mod`` / ``add`` 是新值；``del`` 是被删部分的旧值。
    :param pi_K: 只有 ``del`` 需要 —— 新摘要 :math:`\\delta'` 就是它。
    """

    __slots__ = ("op", "K", "S_K", "F_K", "pi_K")

    def __init__(self, op, K=(), S_K=None, F_K=(), pi_K=None):
        self.op = op
        self.K = as_index_set(K)
        self.S_K = S_K
        self.F_K = tuple(F_K)
        self.pi_K = pi_K

    def verify(
        self, primegen, N: int, U_old: int
    ) -> tuple[bool, str]:
        """校验更新密钥，对应 ``ApplyUpdate`` 的第一步 ``b ← (S_K^{∏ e_j} = U)``。

        三种 ``op`` 的右端项不同：

        * ``mod`` / ``del``：:math:`S_K` 是 **K 在当前版本**上的成员见证，
          所以 :math:`S_K^{e_K} = U`；
        * ``add``：K 是**新**位置，它在旧文件里的见证就是旧的 :math:`U` 本身，
          :math:`S_K^{e_K} = U^{e_K} = U'`。

          论文 §8.2 把这一行也写成 ``= U``，与它自己前一行
          ``U′ ← U^{∏_{i∈K} e_i}`` 矛盾（该节正文的记号与 §5.2 不一致）。
          这里按代数上自洽的形式取 ``= U'``。

        :returns: ``(b, 说明)``；``b`` 为假时说明写清了失败原因
        """
        if self.S_K is None:
            return False, "Υ∆ 里没有更新密钥 S_K"
        if not self.K:
            return False, "Υ∆ 的 K 为空"

        e_K = e_of(primegen, self.K)
        lhs = pow(int(self.S_K), e_K, N)

        if self.op == "add":
            rhs, name = pow(int(U_old), e_K, N), "U′"
        elif self.op in ("mod", "del"):
            rhs, name = int(U_old), "U"
        else:
            return False, f"未知的 op {self.op!r}"

        if lhs != rhs:
            return False, (
                f"Υ∆ 校验失败：S_K^(e_K) ≠ {name}。"
                f"S_K 不是 K={list(self.K)} 在当前版本上的成员见证 —— "
                f"可能是旧版本的见证，或者被伪造"
            )
        return True, ""

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"UpdateWitness(op={self.op!r}, K={list(self.K)})"


class UpdateDelta:
    """``∆`` —— 一次更新操作的内容描述。

    :param op: ``"mod"`` / ``"add"`` / ``"del"``
    :param K: 被改动的下标
    :param F_new: ``K`` 上的新值；``del`` 时为空
    """

    __slots__ = ("op", "K", "F_new")

    def __init__(self, op, K=(), F_new=()):
        self.op = op
        self.K = as_index_set(K)
        self.F_new = tuple(F_new)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"UpdateDelta(op={self.op!r}, K={list(self.K)})"


def _as_merge_source(other):
    r"""把合并的来源统一成 ``(I, F_I, \pi_I, 标签, 是不是「裸凭证」)``。

    ``StrgNode.AddStorage`` 在论文里的签名是
    ``AddStorage(δ, st, I, F, Q, F_Q, π_Q)`` —— 第二个参数允许只给一份
    **凭证** :math:`(Q, F_Q, \pi_Q)`，而不是一个完整的节点对象。
    本节把三种写法归一：

    * :class:`StorageNode` —— ``(I, F_I, \pi_I)`` 全都有，标签取 ``node_id``
    * :class:`~vds.client_node.Certificate` —— 恰好就是 ``(Q, F_Q, \pi_Q)``
    * 三元组 ``(Q, F_Q, \pi_Q)``

    归一之后合并逻辑只写一份 —— 数学仍然只有 :func:`svc.agg` 那一处，
    这里只负责**取字段**。

    :raises TypeError: 来源不是上述任何一种
    """
    if isinstance(other, StorageNode):
        return other.I, other.FI, other.st, other.node_id, False

    if isinstance(other, Opening):
        raise TypeError(
            "合并来源不能是一个 Opening —— 要的是「下标 + 值 + 证明」三件套"
            "（StorageNode / Certificate / (Q, F_Q, pi_Q)）"
        )

    if hasattr(other, "pi_Q") and hasattr(other, "F_Q"):
        Q = getattr(other, "Q", ())
        F_Q = getattr(other, "F_Q")
        pi_Q = getattr(other, "pi_Q")
        label = getattr(other, "source", "") or "凭证"
    elif isinstance(other, (tuple, list)) and len(other) == 3:
        Q, F_Q, pi_Q = other
        label = "凭证"
    else:
        raise TypeError(
            "AddStorage 的来源必须是一个 StorageNode、一份检索凭证"
            "（有 Q / F_Q / pi_Q），或 (Q, F_Q, pi_Q) 三元组"
            f"（收到 {type(other).__name__}）"
        )
    return as_index_set(Q), tuple(F_Q), pi_Q, label, True


class StorageNode:
    """一个存储节点，持有文件的一部分 ``(I, F_I)`` 与对应的证据 ``π_I``。

    :param node_id: 节点标识（仅用于展示）
    :param session: 所属的 :class:`~vds.vds.VDSSession`，用来拿 ``pp`` 与 ``crs_n``
    :param view: 初始本地视图
    """

    def __init__(self, node_id: str, session: "VDSSession", view: LocalView):
        self.node_id = node_id
        self.session = session
        self.view = view

    # -- 只读便捷属性 -------------------------------------------------------

    @property
    def I(self) -> tuple[int, ...]:
        return self.view.I

    @property
    def FI(self) -> tuple[int, ...]:
        return self.view.FI

    @property
    def delta(self) -> Digest:
        return self.view.delta

    @property
    def st(self) -> Opening:
        return self.view.st

    def crs_n(self) -> CRSn:
        return self.session.crs_n_for(self.view.delta)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"StorageNode({self.node_id!r}, {self.view!r})"

    # -------------------------------------------------------------------
    # 正确性检查
    # -------------------------------------------------------------------

    def check_local_view(self) -> bool:
        """检查「本节点确实老实存着它声称的那部分数据」。

        方案正确性证明里给的判据是
        :math:`st_1^{a_I} = \\delta_1 \\wedge st_2^{b_I} = \\delta_2`。
        换成 §5.2 的记号，这**正好就是** :func:`svc.verify` 的两步校验 ——
        所以直接复用同一个验证器即可，不需要另写一套。

        这一步在 VDS 里很有用：客户端可以随时抽查任意一个节点，
        确认它没有偷偷丢数据或改数据。
        """
        report = svc_verify(
            self.crs_n(),
            self.view.delta.C,
            list(self.view.I),
            list(self.view.FI),
            self.view.st,
        )
        return report.ok

    # -------------------------------------------------------------------
    # StrgNode.AddStorage —— 合并
    # -------------------------------------------------------------------

    def add_storage(
        self,
        other,
        *,
        verify_cert: bool = True,
    ) -> "StorageNode":
        r"""``StrgNode.AddStorage`` —— 把另一份存储（或一份检索凭证）合并进来。

        论文原文::

            S_{I∪Q} ← ShamirTrick(S_I, S_Q, ∏_{i∈I} e_i, ∏_{i∈Q} e_i)
            Λ_{I∪Q} ← VC.Agg((S_I, S_J), (I, F_I, Λ_I), (J, F_J, Λ_J))

        换成 §5.2 的 :func:`svc.agg` 就是一次调用。前提是两份存储
        **不相交**；有重叠时先 :meth:`rmv_storage` 去掉重叠部分。

        :param other: 另一个 :class:`StorageNode`，**或者**一份检索凭证
                      —— :class:`~vds.client_node.Certificate` 或三元组
                      ``(Q, F_Q, \pi_Q)``。论文给这个算法的签名本来就是
                      ``AddStorage(δ, st, I, F, Q, F_Q, π_Q)``，
                      §7 的意图是「任何人拿到一份合法凭证都能成为存储节点」，
                      所以第二个参数不应当强制要求一个 :class:`StorageNode`。
                      两条入口走的是**同一个** :func:`svc.agg`，数学只有一份。
        :param verify_cert: 传凭证时才有意义。默认先按本节点的摘要验一遍凭证
                            （直接复用 :func:`svc.verify`）。不验就合并，
                            等于把一个**来源不明**的份额塞进本地视图，
                            本节点会被悄悄毒掉 —— 而 :meth:`check_local_view`
                            要等到事后抽查才会发现。
        :raises ValueError: 下标重叠、摘要不一致，或凭证没通过验证
        :returns: 一个新的 :class:`StorageNode`（不修改原节点）
        """
        other_I, other_FI, other_st, label, is_cert = _as_merge_source(other)

        if set(self.I) & set(other_I):
            raise ValueError(
                "AddStorage 要求两份存储不相交；有重叠时请先 rmv_storage 去掉重叠"
            )

        if is_cert:
            if len(other_I) != len(other_FI):
                raise ValueError(
                    f"凭证里 Q（{len(other_I)} 个下标）与 "
                    f"F_Q（{len(other_FI)} 个值）长度不一致"
                )
            if verify_cert:
                report = svc_verify(
                    self.crs_n(),
                    self.view.delta.C,
                    list(other_I),
                    list(other_FI),
                    other_st,
                )
                if not report.ok:
                    raise ValueError(
                        f"凭证没有通过本节点摘要的验证，拒绝合并：{report.message}"
                    )
        elif self.view.delta != other.view.delta:
            raise ValueError("两个节点的摘要不同，不能合并")

        crs_n = self.crs_n()
        merged = agg(
            crs_n,
            list(self.I),
            list(self.FI),
            self.st,
            list(other_I),
            list(other_FI),
            other_st,
        )
        # 值要从**两边一起**取：merged.I 是并集，
        # 单看 self.view 会因为缺 other 那部分而下标不存在。
        valmap = dict(zip(self.I, self.FI))
        valmap.update(dict(zip(other_I, other_FI)))
        return StorageNode(
            f"{self.node_id}+{label}",
            self.session,
            LocalView(
                delta=self.view.delta,
                st=merged,
                I=merged.I,
                FI=tuple(valmap[i] for i in merged.I),
            ),
        )

    @classmethod
    def from_certificate(
        cls,
        node_id: str,
        session: "VDSSession",
        delta: Digest,
        cert,
        *,
        verify: bool = True,
    ) -> "StorageNode":
        r"""从一份检索凭证**直接成为**一个存储节点。

        :meth:`add_storage` 解决的是「已经有节点了，再合并一份凭证」；
        这里解决的是「手里只有一份凭证，从头建立一个节点」——
        也就是 §7 那句「任何人拿到一份合法凭证都能成为存储节点」。
        本地视图就是 ``(δ, π_Q, Q, F_Q)``，不需要别的材料。

        :param cert: :class:`~vds.client_node.Certificate`，或任意带
                     ``Q`` / ``F_Q`` / ``pi_Q`` 三个属性的对象，
                     或三元组 ``(Q, F_Q, \pi_Q)``
        :param verify: 是否先验一遍凭证（复用 :func:`svc.verify`）；
                       默认开 —— 摘要本来就拿在手里，验一次几乎免费
        :raises ValueError: 凭证没通过验证
        """
        Q, F_Q, pi_Q, _label, _is_cert = _as_merge_source(cert)
        if verify:
            report = svc_verify(
                session.crs_n_for(delta), delta.C, list(Q), list(F_Q), pi_Q
            )
            if not report.ok:
                raise ValueError(
                    f"凭证没有通过摘要的验证，不建立节点：{report.message}"
                )
        return cls(
            node_id,
            session,
            LocalView(delta=delta, st=pi_Q, I=as_index_set(Q), FI=tuple(F_Q)),
        )

    # -------------------------------------------------------------------
    # StrgNode.RmvStorage —— 删除一部分
    # -------------------------------------------------------------------

    def rmv_storage(self, K: Sequence[int]) -> "StorageNode":
        """``StrgNode.RmvStorage`` —— 丢掉一部分数据。

        论文原文::

            S_J ← S_I^{∏_{i∈I∩K} e_i},  Λ_J ← VC.Disagg(S_J, I, F_I, Λ_I, J)

        其中 ``J = I \\ K``。注意 :math:`S_I^{e_{I \\cap K}} = g^{e_{[n]}/e_I \\cdot e_{I\\cap K}}
        = g^{e_{[n]}/e_{I \\setminus K}} = S_{I \\setminus K}`，
        因为两种写法都把 :math:`I \\cap K` 那部分素数约掉了 ——
        即丢掉一部分数据后，剩下的证据不需要重算，拆一次就行。

        :returns: 一个新的 :class:`StorageNode`，只持有 ``I \\ K``
        """
        K_set = as_index_set(K)
        if not set(K_set) <= set(self.I):
            raise ValueError("要删除的下标必须都在本地集合里")

        keep = [i for i in self.I if i not in set(K_set)]
        if not keep:
            raise ValueError("删除后什么都不剩了，节点应直接下线")

        crs_n = self.crs_n()
        pi_keep = disagg(
            crs_n,
            list(self.I),
            list(self.FI),
            self.st,
            keep,
        )
        return StorageNode(
            f"{self.node_id}\\{list(K_set)}",
            self.session,
            LocalView(
                delta=self.view.delta,
                st=pi_keep,
                I=tuple(keep),
                FI=tuple(self.view.value_of(i) for i in keep),
            ),
        )

    # -------------------------------------------------------------------
    # StrgNode.Retrieve —— 检索
    # -------------------------------------------------------------------

    def retrieve(self, Q: Sequence[int]) -> tuple[tuple[int, ...], Opening]:
        """``StrgNode.Retrieve`` —— 返回请求的部分内容与对应证据。

        :param Q: 请求的下标集合，必须 :math:`Q \\subseteq I`
        :returns: ``(F_Q, π_Q)``，其中 :math:`\\pi_Q` 由 :func:`svc.disagg` 一次拆出

        返回的 :math:`\\pi_Q` 是**一个合法的子向量打开证明**，
        客户端拿它配合摘要就能独立验证，不需要信任本节点。
        """
        Q_set = as_index_set(Q)
        if not set(Q_set) <= set(self.I):
            missing = sorted(set(Q_set) - set(self.I))
            raise ValueError(f"本节点不持有下标 {missing}，无法满足检索请求")

        crs_n = self.crs_n()
        pi_Q = disagg(crs_n, list(self.I), list(self.FI), self.st, Q_set)
        F_Q = tuple(self.view.value_of(i) for i in Q_set)
        return F_Q, pi_Q

    def has(self, Q: Sequence[int]) -> bool:
        """是否持有 ``Q`` 的全部下标。"""
        return self.view.has(Q)

    # -------------------------------------------------------------------
    # StrgNode.PoS-Prove / PoS-Aggregate（附录 D.1）
    # -------------------------------------------------------------------

    def pos_prove(self, challenge) -> "PoSProof":
        """``StrgNode.PoS-Prove`` —— 回答存储证明挑战里落在本节点的那段。

        只答 ``Q = I ∩ r``，不需要（也拿不到）别的节点的份额。
        挑战没打到本节点时返回空证明。
        """
        from .pos import pos_prove

        return pos_prove(self, challenge)

    def pos_aggregate(self, challenge, left, right) -> "tuple[bool, PoSProof]":
        """``StrgNode.PoS-Aggregate`` —— 把两份部分证明合成一份。

        :returns: ``(b, π_r)``；``b = 1`` 表示已覆盖整个挑战
        """
        from .pos import pos_aggregate

        return pos_aggregate(self.crs_n(), challenge, left, right)

    # -------------------------------------------------------------------
    # StrgNode.CreateFrom —— 本方案不支持
    # -------------------------------------------------------------------

    def create_from(self, J: Sequence[int]) -> tuple[Digest, "StorageNode"]:
        r"""``StrgNode.CreateFrom`` —— **本方案不支持「派生新文件」**。

        .. note::

           本方案（§5.2）把承诺压成了单个群元素，**这正是它参数更省的原因**，
           代价就是失去了子向量知识论证赖以存在的代数结构。
           所以这里不实现它。（主流程 commit → 分发 → 检索 → 聚合 → 验证
           本来就不依赖它。）

        论文原文（对照用）::

            δ′ ← VC.Com′(pp, F_J)          ← 对新子文件重新做一次承诺
            n′ ← |J|
            st′ ← VC.Disagg(pp, I, F_I, π_I, J)
            Υ_J ← (δ′, π_PoKSubV′)

        .. warning::

           这个算法的意义**全部**在于那份子向量知识论证 ——
           它用来向客户端证明「我这个新摘要确实是从原文件的某个子向量
           切出来的，没有夹带私货」。若把那部分省掉，:math:`\delta'` 与
           :math:`st'` 仍能算出来，但客户端**无从核实**，算法就失去了意义。

           它依赖四样东西，本方案一样都没有：

           * CRS 里有**两个**生成元 :math:`(g_0, g_1)`（本方案只有一个 :math:`g`）
           * 承诺是**一对**累加器 :math:`C := (\{A,B\},\ \pi_{\text{prod}})`
             （本方案的 :math:`C` 是单个群元素）
           * :math:`\mathsf{PartndPrimeProd}(I,\vec{v}_I)\to(a_I,b_I)`
             —— 把 :math:`I` 里的素数按「该位是 0 还是 1」分成两堆
             （本方案没有二元划分）
           * 打开证明是 :math:`(\Gamma_I, \Delta_I)` 一对
             （本方案是 :math:`(S_I,\Lambda_I)`）

           整套机制建立在「承诺是一对累加器 :math:`A,B`」之上 —— 有了这一对，
           才能把 :math:`(a_I,b_I)` 分别塞进两条等式里做 AND 复合。
        """
        raise NotImplementedError(
            "本方案（§5.2 单生成元 SVC）不支持从已存文件派生新文件："
            "缺少子向量知识论证所需的双生成元与双累加器结构。"
        )
