<<<<<<< HEAD
"""客户端节点 —— 论文 §7 的 ``ClntNode`` 算法族。

客户端**只持有摘要** :math:`\\delta = ((U, C), n)`（两个群元素 + 一个整数），
不持有文件内容。它要回答的问题是：

    我从若干个互不信任的存储节点那里取回了一堆分片和证据，
    怎么一次确认**所有**分片都没被篡改？

答案分两步，正是论文 §8.2 的两条流水线：

1. :meth:`ClientNode.aggregate_certificates` —— ``AggregateCertificates``，
   把多份 :math:`\\pi_{Q_1}, \\dots, \\pi_{Q_k}` 合成**一个** :math:`\\pi_K`；
2. :meth:`ClientNode.ver_retrieve` —— ``ClntNode.VerRetrieve``，
   用摘要校验这一个 :math:`\\pi_K`。

关键的省法：合成之后**只验一次**，而不是每份验一次。
而且验证代价与块数、与文件总长度都无关 ——
:math:`\\pi_K` 永远是两个群元素。
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Sequence

from svc import Opening, VerifyReport, agg_many_to_one, verify as svc_verify
from svc.types import as_index_set

if TYPE_CHECKING:  # pragma: no cover
    from .digest import Digest
    from .vds import VDSSession

__all__ = ["ClientNode", "Certificate"]


class Certificate:
    """一份「检索凭证」：一段内容加上它的子向量打开证明。

    :param Q: 这一段覆盖的下标集合
    :param F_Q: 对应的值
    :param pi_Q: 对应的 :math:`\\pi_Q = (S_Q, \\Lambda_Q)`
    :param source: 来源节点标识（仅用于展示/审计）
    """

    __slots__ = ("Q", "F_Q", "pi_Q", "source")

    def __init__(self, Q: Sequence[int], F_Q: Sequence[int], pi_Q: Opening, source: str = ""):
        self.Q = as_index_set(Q)
        self.F_Q = tuple(F_Q)
        self.pi_Q = pi_Q
        self.source = source

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"Certificate(|Q|={len(self.Q)}, from={self.source!r})"


class ClientNode:
    """客户端。持有摘要，负责聚合凭证与验证。"""

    def __init__(self, session: "VDSSession", delta: "Digest"):
        self.session = session
        self.delta = delta

    # -------------------------------------------------------------------
    # AggregateCertificates
    # -------------------------------------------------------------------

    def aggregate_certificates(self, certs: Sequence[Certificate]) -> Opening:
        """``AggregateCertificates`` —— 把多份凭证合成**一个**证明。

        论文原文::

            AggregateCertificates(δ, (I, F_I, π_I), (J, F_J, π_J)) → π_K
                Return π_K ← VC.Agg′(pp, (I, F⃗_I, π_I), (J, F⃗_J, π_J))

        :returns: 覆盖 :math:`K = \\bigcup Q_i` 的单个证明 :math:`\\pi_K`

        :raises ValueError: 两份凭证覆盖了同一下标（:func:`svc.agg` 要求不相交）。
                            正常情况下不同存储节点负责不同区块，不会重叠；
                            真有重叠时应当先用 :func:`svc.disagg` 去掉再合。
        """
        if not certs:
            raise ValueError("凭证列表为空")
        if len(certs) == 1:
            return certs[0].pi_Q

        crs_n = self.session.crs_n_for(self.delta)
        return agg_many_to_one(
            crs_n,
            [(c.Q, c.F_Q, c.pi_Q) for c in certs],
        )

    # -------------------------------------------------------------------
    # VerRetrieve
    # -------------------------------------------------------------------

    def ver_retrieve(
        self,
        Q: Sequence[int],
        F_Q: Sequence[int],
        pi_K: Opening,
    ) -> VerifyReport:
        """``ClntNode.VerRetrieve`` —— 用摘要校验一份（通常是聚合后的）证明。

        论文原文::

            ClntNode.VerRetrieve(δ, Q, F_Q, π_Q) → b
                Output b ← VC.Ver′(pp, δ, Q, F_Q, π_Q)

        换成 §5.2 就是 :func:`svc.verify`：

        .. math::
            S_Q^{e_Q} = U  \\quad \\wedge \\quad
            C = \\Lambda_Q^{e_Q} \\cdot \\prod_{i \\in Q} S_i^{F_i}

        注意 :math:`U` 和 :math:`C` 都来自摘要，**不需要**再向任何节点索取东西 ——
        这就是「客户端只需保存一个常数量摘要」的全部含义。

        :returns: :class:`~svc.VerifyReport`，``.code`` 指明失败环节
        """
        crs_n = self.session.crs_n_for(self.delta)
        return svc_verify(crs_n, self.delta.C, list(Q), list(F_Q), pi_K)

    # -------------------------------------------------------------------
    # 便捷封装
    # -------------------------------------------------------------------

    def retrieve_and_verify(
        self,
        certs: Sequence[Certificate],
    ) -> tuple[tuple[int, ...], tuple[int, ...], VerifyReport]:
        """把「聚合 + 验证」串起来跑一遍，返回 ``(Q, F_Q, 报告)``。

        这是前端「检索」按钮背后实际调用的东西。
        """
        pi_K = self.aggregate_certificates(certs)
        Q = as_index_set([i for c in certs for i in c.Q])
        # 按下标顺序把各段的值拼起来
        valmap: dict[int, int] = {}
        for c in certs:
            valmap.update(dict(zip(c.Q, c.F_Q)))
        F_Q = tuple(valmap[i] for i in Q)
        return Q, F_Q, self.ver_retrieve(Q, F_Q, pi_K)

    # -------------------------------------------------------------------
    # ClntNode.PoS-Challenge / PoS-Ver（附录 D.1）
    # -------------------------------------------------------------------

    def pos_challenge(self, lambda_pos: int | None = None, rng=None):
        """``ClntNode.PoS-Challenge`` —— 生成一份存储证明挑战。

        只需要文件长度 ``δ.n``，不需要文件内容。
        """
        from .pos import DEFAULT_LAMBDA_POS, pos_challenge

        return pos_challenge(
            self.delta.n,
            DEFAULT_LAMBDA_POS if lambda_pos is None else lambda_pos,
            rng,
        )

    def pos_ver(self, challenge, proof) -> VerifyReport:
        """``ClntNode.PoS-Ver`` —— 验证收齐的存储证明。

        两道判据：``Q = r`` 且 ``VerRetrieve`` 通过。
        """
        from .pos import pos_ver

        return pos_ver(self, challenge, proof)

    # -------------------------------------------------------------------
    # ClntNode.GetCreate —— 需要 PoKSubV，未实现
    # -------------------------------------------------------------------

    def get_create(self, J, Upsilon_J=None):
        r"""``ClntNode.GetCreate`` —— **属于 §8.1 的 ``VDS1``，不在本方案里**。

        论文原文::

            ClntNode.GetCreate(δ, J, Υ_J) → (b, δ′)
                Parse Υ_J := (δ′, π_PoKSubV′), set n′ = |J|
                Output b ← PoKSubV′.V(pp, (δ, δ′, J), π_J)
                            ∧ J = {1, ..., |J|} ∧ δ′

        .. note::

           它依赖论文 §6 的子向量知识论证 ``PoKSubV``，而 ``PoKSubV``
           **建立在 §5.1 阴阳方案之上**（CRS 有两个生成元
           :math:`g_0,g_1`、承诺是一对累加器、依赖二元划分
           :math:`\mathsf{PartndPrimeProd}`）。
           §5.2 把承诺压成单个群元素（这正是它参数更省的原因），
           也就失去了这套代数结构。

           §5.1 与 §6 现在已经完整实现（``svc/yinyan.py`` 与 ``svc/pok.py``）。
           对应的 ``GetCreate`` 在 :meth:`vds.vds1.ClientNode1.get_create`，
           配套的派生端在 :meth:`vds.vds1.StorageNode1.create_from`。
           完整走一遍：``python demo/vds1_create_from.py``。
        """
        raise NotImplementedError(
            "ClntNode.GetCreate 属于论文 §8.1 的 VDS1，不在 §8.2 的 VDS2 里。"
            "请改用 vds.vds1.ClientNode1.get_create；"
            "配套的派生端是 vds.vds1.StorageNode1.create_from。"
            "参见 demo/vds1_create_from.py。"
        )
=======
"""客户端节点 —— 论文 §7 的 ``ClntNode`` 算法族。

客户端**只持有摘要** :math:`\\delta = ((U, C), n)`（两个群元素 + 一个整数），
不持有文件内容。它要回答的问题是：

    我从若干个互不信任的存储节点那里取回了一堆分片和证据，
    怎么一次确认**所有**分片都没被篡改？

答案分两步，正是论文 §8.2 的两条流水线：

1. :meth:`ClientNode.aggregate_certificates` —— ``AggregateCertificates``，
   把多份 :math:`\\pi_{Q_1}, \\dots, \\pi_{Q_k}` 合成**一个** :math:`\\pi_K`；
2. :meth:`ClientNode.ver_retrieve` —— ``ClntNode.VerRetrieve``，
   用摘要校验这一个 :math:`\\pi_K`。

关键的省法：合成之后**只验一次**，而不是每份验一次。
而且验证代价与块数、与文件总长度都无关 ——
:math:`\\pi_K` 永远是两个群元素。
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Sequence

from svc import Opening, VerifyReport, agg_many_to_one, verify as svc_verify
from svc.types import as_index_set

if TYPE_CHECKING:  # pragma: no cover
    from .digest import Digest
    from .vds import VDSSession

__all__ = ["ClientNode", "Certificate"]


class Certificate:
    """一份「检索凭证」：一段内容加上它的子向量打开证明。

    :param Q: 这一段覆盖的下标集合
    :param F_Q: 对应的值
    :param pi_Q: 对应的 :math:`\\pi_Q = (S_Q, \\Lambda_Q)`
    :param source: 来源节点标识（仅用于展示/审计）
    """

    __slots__ = ("Q", "F_Q", "pi_Q", "source")

    def __init__(self, Q: Sequence[int], F_Q: Sequence[int], pi_Q: Opening, source: str = ""):
        self.Q = as_index_set(Q)
        self.F_Q = tuple(F_Q)
        self.pi_Q = pi_Q
        self.source = source

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"Certificate(|Q|={len(self.Q)}, from={self.source!r})"


class ClientNode:
    """客户端。持有摘要，负责聚合凭证与验证。"""

    def __init__(self, session: "VDSSession", delta: "Digest"):
        self.session = session
        self.delta = delta

    # -------------------------------------------------------------------
    # AggregateCertificates
    # -------------------------------------------------------------------

    def aggregate_certificates(self, certs: Sequence[Certificate]) -> Opening:
        """``AggregateCertificates`` —— 把多份凭证合成**一个**证明。

        论文原文::

            AggregateCertificates(δ, (I, F_I, π_I), (J, F_J, π_J)) → π_K
                Return π_K ← VC.Agg′(pp, (I, F⃗_I, π_I), (J, F⃗_J, π_J))

        :returns: 覆盖 :math:`K = \\bigcup Q_i` 的单个证明 :math:`\\pi_K`

        :raises ValueError: 两份凭证覆盖了同一下标（:func:`svc.agg` 要求不相交）。
                            正常情况下不同存储节点负责不同区块，不会重叠；
                            真有重叠时应当先用 :func:`svc.disagg` 去掉再合。
        """
        if not certs:
            raise ValueError("凭证列表为空")
        if len(certs) == 1:
            return certs[0].pi_Q

        crs_n = self.session.crs_n_for(self.delta)
        return agg_many_to_one(
            crs_n,
            [(c.Q, c.F_Q, c.pi_Q) for c in certs],
        )

    # -------------------------------------------------------------------
    # VerRetrieve
    # -------------------------------------------------------------------

    def ver_retrieve(
        self,
        Q: Sequence[int],
        F_Q: Sequence[int],
        pi_K: Opening,
    ) -> VerifyReport:
        """``ClntNode.VerRetrieve`` —— 用摘要校验一份（通常是聚合后的）证明。

        论文原文::

            ClntNode.VerRetrieve(δ, Q, F_Q, π_Q) → b
                Output b ← VC.Ver′(pp, δ, Q, F_Q, π_Q)

        换成 §5.2 就是 :func:`svc.verify`：

        .. math::
            S_Q^{e_Q} = U  \\quad \\wedge \\quad
            C = \\Lambda_Q^{e_Q} \\cdot \\prod_{i \\in Q} S_i^{F_i}

        注意 :math:`U` 和 :math:`C` 都来自摘要，**不需要**再向任何节点索取东西 ——
        这就是「客户端只需保存一个常数量摘要」的全部含义。

        :returns: :class:`~svc.VerifyReport`，``.code`` 指明失败环节
        """
        crs_n = self.session.crs_n_for(self.delta)
        return svc_verify(crs_n, self.delta.C, list(Q), list(F_Q), pi_K)

    # -------------------------------------------------------------------
    # 便捷封装
    # -------------------------------------------------------------------

    def retrieve_and_verify(
        self,
        certs: Sequence[Certificate],
    ) -> tuple[tuple[int, ...], tuple[int, ...], VerifyReport]:
        """把「聚合 + 验证」串起来跑一遍，返回 ``(Q, F_Q, 报告)``。

        这是前端「检索」按钮背后实际调用的东西。
        """
        pi_K = self.aggregate_certificates(certs)
        Q = as_index_set([i for c in certs for i in c.Q])
        # 按下标顺序把各段的值拼起来
        valmap: dict[int, int] = {}
        for c in certs:
            valmap.update(dict(zip(c.Q, c.F_Q)))
        F_Q = tuple(valmap[i] for i in Q)
        return Q, F_Q, self.ver_retrieve(Q, F_Q, pi_K)

    # -------------------------------------------------------------------
    # ClntNode.PoS-Challenge / PoS-Ver（附录 D.1）
    # -------------------------------------------------------------------

    def pos_challenge(self, lambda_pos: int | None = None, rng=None):
        """``ClntNode.PoS-Challenge`` —— 生成一份存储证明挑战。

        只需要文件长度 ``δ.n``，不需要文件内容。
        """
        from .pos import DEFAULT_LAMBDA_POS, pos_challenge

        return pos_challenge(
            self.delta.n,
            DEFAULT_LAMBDA_POS if lambda_pos is None else lambda_pos,
            rng,
        )

    def pos_ver(self, challenge, proof) -> VerifyReport:
        """``ClntNode.PoS-Ver`` —— 验证收齐的存储证明。

        两道判据：``Q = r`` 且 ``VerRetrieve`` 通过。
        """
        from .pos import pos_ver

        return pos_ver(self, challenge, proof)

    # -------------------------------------------------------------------
    # ClntNode.GetCreate —— 本方案不支持
    # -------------------------------------------------------------------

    def get_create(self, J, Upsilon_J=None):
        r"""``ClntNode.GetCreate`` —— **本方案不支持「派生新文件」**。

        「从一个已存文件派生出新文件」这个能力，其正确性完全依赖一份
        子向量知识论证：节点必须向客户端证明「这个新摘要确实是从原文件的
        某个子向量切出来的，没有夹带私货」。

        那套论证需要下面四样东西，本方案（§5.2 的单生成元 SVC）一样都没有：

        * CRS 里有**两个**生成元 :math:`(g_0, g_1)`（本方案只有一个 :math:`g`）
        * 承诺是**一对**累加器 :math:`(A, B)`（本方案的 :math:`C` 是单个群元素）
        * 二元划分 :math:`\mathsf{PartndPrimeProd}`（本方案没有）
        * 打开证明是**一对** :math:`(\Gamma_I, \Delta_I)`（本方案是 :math:`(S_I, \Lambda_I)`）

        本方案把承诺压成单个群元素，**这正是它参数更省的原因**，
        代价就是失去了那套代数结构。
        所以这里显式报错，而不是返回一个客户端根本无法核实的假派生。
        """
        raise NotImplementedError(
            "本方案（§5.2 单生成元 SVC）不支持从已存文件派生新文件："
            "缺少子向量知识论证所需的双生成元与双累加器结构。"
        )
>>>>>>> main
