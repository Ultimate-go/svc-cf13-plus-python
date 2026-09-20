"""存储节点 —— 论文 §7 的 ``StrgNode`` 算法族。

本模块实现与「检索 + 聚合 + 验证」这条主流程直接相关的算法：

======================  ====================================================
论文算法                 本模块
======================  ====================================================
``StrgNode.AddStorage``  :meth:`StorageNode.add_storage` —— 合并另一份存储
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
    from .vds import VDSSession

__all__ = ["StorageNode", "UpdateWitness", "UpdateDelta"]


class UpdateWitness:
    """``Υ∆``：存储节点交给客户端的更新见证。"""

    __slots__ = ("op", "K", "F_K", "S_K", "pi_K")

    def __init__(self, op: str, K=(), F_K=(), S_K: int | None = None, pi_K=None):
        self.op = op
        self.K = as_index_set(K)
        self.F_K = tuple(F_K)
        self.S_K = S_K
        self.pi_K = pi_K

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"UpdateWitness(op={self.op!r}, K={list(self.K)})"


class UpdateDelta:
    """``∆``：一次更新操作的内容描述。"""

    __slots__ = ("op", "K", "F_new")

    def __init__(self, op: str, K=(), F_new=()):
        self.op = op
        self.K = as_index_set(K)
        self.F_new = tuple(F_new)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"UpdateDelta(op={self.op!r}, K={list(self.K)})"


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

        论文 VDS1 正确性证明里给的判据是
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
        other: "StorageNode",
    ) -> "StorageNode":
        """``StrgNode.AddStorage`` —— 把另一个节点持有的部分合并进来。

        论文原文::

            S_{I∪Q} ← ShamirTrick(S_I, S_Q, ∏_{i∈I} e_i, ∏_{i∈Q} e_i)
            Λ_{I∪Q} ← VC.Agg((S_I, S_J), (I, F_I, Λ_I), (J, F_J, Λ_J))

        换成 §5.2 的 :func:`svc.agg` 就是一次调用。前提是两份存储
        **不相交**；有重叠时先 :meth:`rmv_storage` 去掉重叠部分。

        :returns: 一个新的 :class:`StorageNode`（不修改原节点）
        """
        if set(self.I) & set(other.I):
            raise ValueError(
                "AddStorage 要求两份存储不相交；有重叠时请先 rmv_storage 去掉重叠"
            )
        if self.view.delta != other.view.delta:
            raise ValueError("两个节点的摘要不同，不能合并")

        crs_n = self.crs_n()
        merged = agg(
            crs_n,
            list(self.I),
            list(self.FI),
            self.st,
            list(other.I),
            list(other.FI),
            other.st,
        )
        # 值要从**两边一起**取：merged.I 是并集，
        # 单看 self.view 会因为缺 other 那部分而下标不存在。
        valmap = dict(zip(self.I, self.FI))
        valmap.update(dict(zip(other.I, other.FI)))
        return StorageNode(
            f"{self.node_id}+{other.node_id}",
            self.session,
            LocalView(
                delta=self.view.delta,
                st=merged,
                I=merged.I,
                FI=tuple(valmap[i] for i in merged.I),
            ),
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
        也就是说**丢掉一部分数据后，剩下的证据不需要重算**，拆一次就行。

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
    # StrgNode.CreateFrom —— 从大文件派生小文件
    # -------------------------------------------------------------------

    def create_from(self, J: Sequence[int]) -> tuple[Digest, "StorageNode"]:
        r"""``StrgNode.CreateFrom`` —— 用手里的一部分数据「另立门户」（**未实现**）。

        论文原文::

            δ′ ← VC.Com′(pp, F_J)          ← 对新子文件重新做一次承诺
            n′ ← |J|
            st′ ← VC.Disagg(pp, I, F_I, π_I, J)
            Υ_J ← (δ′, π_PoKSubV′)

        .. warning::

           **本方法未实现，调用会直接报错**。原因：

           这个算法的意义**全部**在于那个 :math:`\Upsilon_J` ——
           它含一个子向量知识论证 :math:`\pi_{PoKSubV'}`，
           用来向客户端证明「我这个新摘要确实是从原文件的某个子向量切出来的，
           没有夹带私货」。而这个论证是论文 **§6 的独立协议 ``PoKSubV``**，
           不属于 §5.2 的 SVC，本次实现没有覆盖。

           若把 PoK 部分省掉，:math:`\delta'` 与 :math:`st'` 仍能算出来，
           但客户端**无法**核实它，于是 :meth:`~vds.client_node.ClientNode.get_create`
           也就无从完成 —— 这个算法就失去了意义。
           与其返回一个看起来能跑、实际上没人能验证的结果，
           不如在这里直接报错。

           详见 ``docs/与论文对照.md`` 的「未实现部分」。

           主流程（commit → 分发 → 检索 → 聚合 → 验证）**不受影响**。
        """
        raise NotImplementedError(
            "StrgNode.CreateFrom 依赖论文 §6 的 PoKSubV 协议，本实现未包含；"
            "主流程（检索—聚合—验证）不依赖它，可正常使用。"
        )
