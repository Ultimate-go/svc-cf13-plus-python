r"""论文 §8.1 的第一种 VDS —— ``VDS1``。

与 :mod:`vds.vds` 的 ``VDSSession``（§8.2，基于 §5.2 的 SVC）相比，
``VDS1`` 建立在 §5.1 的阴阳方案之上，摘要里带的是**一对**累加器：

.. code-block:: text

    δ  := ((A, B), n)          ← 摘要，客户端只保存它
    st := π_I := (Γ_I, Δ_I)    ← 存储节点的本地状态

这让 :math:`C'` 能"挂"在 :math:`C` 的代数结构上，于是可以拿
:class:`~svc.pok.PoKSubV` 证明"新承诺 `δ'` 承诺的正是 `δ` 在 `J` 上的子向量"。
:meth:`StorageNode1.create_from` / :meth:`ClientNode1.get_create` 这一对算法
就是整个 VDS 里"从一个已存文件派生出一个新文件"的机制 ——
新文件不必重新分发，客户端只用一个常数大小的证明就能确认新摘要的合法性。

与 §8.2 的差别
--------------
=======================  ==========================  ==========================
                         本节 ``VDS1``（§8.1）        :mod:`vds.vds`（§8.2）
=======================  ==========================  ==========================
摘要                      ``((A, B), n)`` 两个群元素   ``((U, C), n)`` 两个群元素
本地状态                  ``(Γ_I, Δ_I)``               ``(S_I, Λ_I)``
``VC.Com``                ``Com'``：无 ``PoProd2``     正常 ``Com``
派生新文件                ``PoKSubV'``（常数大小）      无对应机制
``VC.Specialize``         不需要                       需要（`U_n` 进摘要）
=======================  ==========================  ==========================

``VDS1`` 少了 ``PoProd2`` 的开销，代价是承诺与打开都是**两个**群元素
（§8.2 各一个）。论文 §8.3 对两者做了对比。

论文记号与本模块的对应
----------------------
============================  ==========================================
论文算法                       本模块
============================  ==========================================
``Bootstrap``                 :meth:`VDS1Session.bootstrap`
``VC.Com'``                   :func:`com_prime`
``VC.Ver'``                   :func:`ver_prime`
``VC.Disagg'``                :func:`disagg_prime`
``VC.Agg'``                   :func:`agg_prime`
``StrgNode.AddStorage``       :meth:`StorageNode1.add_storage`
``StrgNode.RmvStorage``       :meth:`StorageNode1.rmv_storage`
``StrgNode.CreateFrom``       :meth:`StorageNode1.create_from`
``StrgNode.PushUpdate``       :meth:`StorageNode1.push_update`
``StrgNode.ApplyUpdate``      :meth:`StorageNode1.apply_update`
``StrgNode.Retrieve``         :meth:`StorageNode1.retrieve`
``ClntNode.GetCreate``        :meth:`ClientNode1.get_create`
``ClntNode.VerRetrieve``      :meth:`ClientNode1.ver_retrieve`
``ClntNode.ApplyUpdate``      :meth:`ClientNode1.apply_update`
``AggregateCertificates``     :meth:`ClientNode1.aggregate_certificates`
============================  ==========================================

一处记号订正
------------
``op = add`` 的 ``PushUpdate`` 论文写 ``st' ← st``，理由是
``π_I = π'_J``。该等式只在 :math:`a'_K = 1`（即新增的块全为「全 1 比特」）时成立；
一般情况下 :math:`\pi'_J = (\Gamma_I^{a'_K}, \Delta_I^{b'_K})`
—— 这正是同节 ``ApplyUpdate`` 给出的公式。本模块统一采用后者，
否则 push 出去的状态与 apply 得到的状态不一致。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence

from svc.mathbase import shamir_trick, product_tree
from svc.pok import PoKSubVProof, Transcript, poksubv_prove, poksubv_verify
from svc.primegen import PrimeGen, PrimeGenHash
from svc.rng import DeterministicRNG
from svc.scheme import DEFAULT_MODULUS_BITS
from svc.types import as_index_set, fingerprint
from svc.yinyan import (
    CRS1,
    Commitment1,
    Opening1,
    agg1,
    agg_many_to_one1,
    disagg1,
    partnd_prime_prod,
    setup1,
)

__all__ = [
    "Digest1",
    "LocalView1",
    "CreateWitness",
    "UpdateOp1",
    "PushedUpdate1",
    "AppliedUpdate1",
    "VDS1Session",
    "StorageNode1",
    "ClientNode1",
    "com_prime",
    "ver_prime",
    "disagg_prime",
    "agg_prime",
    "is_prefix",
    "poksubv_prime_prove",
    "poksubv_prime_verify",
]

#: ``PoKSubV'`` 的转录域分隔标签。
POKSUBV_PRIME_LABEL = "poksubv'"

#: §8.1 的 ``PoKSubV'`` 只用通用 ``crs``，语句里没有 :math:`U_n`。
#: ``svc.pok`` 的实现沿用了 §6 的原版签名，多一个 ``U_n`` 入参；
#: 这里固定填 1，用途仅仅是让两端的转录一致。
_NO_U_N = 1


# ---------------------------------------------------------------------------
# 摘要与本地视图
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Digest1:
    r"""``δ := ((A, B), n)`` —— ``VDS1`` 的文件摘要。

    :param A: :math:`g_0^{a}`，其中 :math:`a = \prod_{i:\,v_i = 0} p_i`
    :param B: :math:`g_1^{b}`，其中 :math:`b = \prod_{i:\,v_i = 1} p_i`
    :param n: 文件的块数

    空文件的约定取值是 ``(g0, g1, 0)``，由 :meth:`VDS1Session.bootstrap` 给出，
    与 ``Com'`` 作用在空向量上的结果一致。
    """

    A: int
    B: int
    n: int

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"Digest1(n={self.n}, A={fingerprint(self.A)}, B={fingerprint(self.B)})"
        )

    def commitment(self) -> Commitment1:
        """转成 :class:`~svc.yinyan.Commitment1`（``k = 1``、不带 ``PoProd2``）。"""
        return Commitment1(A=(self.A,), B=(self.B,), prod=(), n=self.n)

    @classmethod
    def from_commitment(cls, C: Commitment1) -> "Digest1":
        """从 ``k = 1`` 的 :class:`~svc.yinyan.Commitment1` 取摘要。"""
        if C.k != 1:
            raise ValueError(f"VDS1 的摘要只对应 k = 1，收到 k = {C.k}")
        return cls(A=C.A[0], B=C.B[0], n=C.n)


@dataclass
class LocalView1:
    r"""存储节点的本地视图 ``(pp, δ, n, st, I, F_I)``。

    有效性判据（论文 §8.1 正确性证明里给出的那条）：

    .. math::

        st_1^{a_I} = \delta_1 \;\wedge\; st_2^{b_I} = \delta_2

    换成代码就是 :func:`ver_prime`(:math:`\delta, I, F_I, st`) 成立。
    """

    delta: Digest1
    st: Opening1
    I: tuple[int, ...] = ()
    FI: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        self.I = tuple(as_index_set(self.I))
        if len(self.I) != len(self.FI):
            raise ValueError(f"I 有 {len(self.I)} 个位置，但有 {len(self.FI)} 个值")
        # st 与视图必须指向同一组下标，否则 ver_prime 会拿错指数
        if self.st.I and self.I and self.st.I != self.I:
            raise ValueError(
                f"状态 st 对应下标 {list(self.st.I)}，与视图的下标 {list(self.I)} 不一致"
            )

    @property
    def n(self) -> int:
        return self.delta.n

    def value_of(self, i: int) -> int:
        """取下标 ``i`` 的值；不在本地视图里则抛 ``KeyError``。"""
        try:
            return self.FI[self.I.index(i)]
        except ValueError:
            raise KeyError(f"本节点不持有下标 {i}") from None

    def has(self, indices: Iterable[int]) -> bool:
        """是否持有全部给定下标。"""
        held = set(self.I)
        return all(i in held for i in indices)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        head = list(self.I[:8])
        tail = "..." if len(self.I) > 8 else ""
        return f"LocalView1({self.delta!r}, |I|={len(self.I)}, I={head}{tail})"


# ---------------------------------------------------------------------------
# VC.Com' / VC.Ver' / VC.Disagg' / VC.Agg'
# ---------------------------------------------------------------------------

def com_prime(crs: CRS1, vals: Sequence[int]) -> Digest1:
    """``VC.Com'(crs, v) → δ``。

    与 §5.1 的 ``VC.Com`` 唯一的差别是**不生成** ``PoProd2`` 证明：

    .. code-block:: text

        (a, b) ← PartndPrimeProd([n], v)
        δ ← ((g0^a, g1^b), n)

    省掉 ``PoProd2`` 之后承诺小了一半，代价是丢了「两个累加器构成划分」
    这条可验证性质；``VDS1`` 靠 ``PoKSubV'`` 在需要时把这份性质补回来。
    """
    vals = tuple(int(v) for v in vals)
    for v in vals:
        if v < 0 or v >= (1 << crs.k):
            raise ValueError(f"值 {v} 超出 k = {crs.k} 位的范围")
    a, b = partnd_prime_prod(crs.primegen, range(len(vals)), vals, 1)[0]
    return Digest1(
        A=pow(crs.g0, a, crs.N),
        B=pow(crs.g1, b, crs.N),
        n=len(vals),
    )


def ver_prime(
    crs: CRS1,
    delta: Digest1,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening1,
) -> bool:
    """``VC.Ver'(crs, δ, I, y, π_I) → b``。

    .. code-block:: text

        (aI, bI) ← PartndPrimeProd(I, y)
        b ← (Γ_I^{aI} = A) ∧ (Δ_I^{bI} = B)

    注意这里**不检查** ``PoProd2`` —— ``Com'`` 根本没产出它。
    """
    I = as_index_set(I)
    if len(vals_I) != len(I) or pi_I.k != 1:
        return False
    if I and (I[0] < 0 or I[-1] >= delta.n):
        return False
    if pi_I.I and pi_I.I != I:
        return False

    a_I, b_I = partnd_prime_prod(crs.primegen, I, [int(v) for v in vals_I], 1)[0]
    N = crs.N
    if pow(pi_I.Gamma[0], a_I, N) != delta.A % N:
        return False
    return pow(pi_I.Delta[0], b_I, N) == delta.B % N


def disagg_prime(
    crs: CRS1,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening1,
    K: Sequence[int],
) -> Opening1:
    """``VC.Disagg'(crs, I, v_I, π_I, K) → π_K``，要求 ``K ⊆ I``。

    与 §5.1 的版本逐字相同（§8.1 只是把它重新列了一遍），直接转发给
    :func:`~svc.yinyan.disagg1`。
    """
    return disagg1(crs, I, vals_I, pi_I, K)


def agg_prime(
    crs: CRS1,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening1,
    J: Sequence[int],
    vals_J: Sequence[int],
    pi_J: Opening1,
) -> Opening1:
    """``VC.Agg'(crs, (I, v_I, π_I), (J, v_J, π_J)) → π_K``，``K = I ∪ J``。

    转发给 :func:`~svc.yinyan.agg1`；该函数内部已经实现了论文第 1 步
    「``I ∩ J`` 非空就先 disaggregate 掉重叠部分」，以及第 3 步的
    ``ShamirTrick``。
    """
    return agg1(crs, I, vals_I, pi_I, J, vals_J, pi_J)


def is_prefix(J: Sequence[int]) -> bool:
    r"""``J`` 是否恰好是前 ``|J|`` 个下标（论文 ``GetCreate`` 的那条检查）。

    ``PoKSubV'`` 的最后一条等式是 :math:`Q_C^\ell g^{r_c} = U_{n'}`，
    而 :math:`a_J \cdot b_J = u_J`。要让它等于 :math:`u_{n'}`
    （即 :func:`~svc.yinyan.specialize1` 给出的 :math:`U_{n'}`），
    必须 :math:`u_J = u_{n'}`，也就是 ``J`` 恰好是前 ``|J|`` 个下标。
    这是「子向量必须是一个正常向量，而不是一般子向量」的具体体现。

    本项目的下标从 0 开始（与 :func:`~svc.yinyan.specialize1` 里
    ``prime_prod(range(n))`` 的写法一致），因此判据是 ``J = {0, …, |J|-1}``。
    """
    J = as_index_set(J)
    return list(J) == list(range(len(J)))


# ---------------------------------------------------------------------------
# PoKSubV' —— §6 的 PoKSubV 在 VDS1 记号下的简化版
# ---------------------------------------------------------------------------

def _poksubv_prime_transcript(
    crs: CRS1, delta: Digest1, delta_p: Digest1, J: Sequence[int]
) -> Transcript:
    """把语句 ``(crs, (δ, δ', J))`` 全部吸附进转录。

    句柄里带上 ``crs`` 的四个公开量与两个摘要，任何一项被替换都会
    导致挑战素数变化，从而让证明失效。
    """
    J = as_index_set(J)
    return Transcript(
        POKSUBV_PRIME_LABEL,
        crs.N, crs.g, crs.g0, crs.g1,
        delta.n, delta.A, delta.B,
        delta_p.n, delta_p.A, delta_p.B,
        len(J), *J,
    )


def poksubv_prime_prove(
    crs: CRS1,
    delta: Digest1,
    delta_p: Digest1,
    J: Sequence[int],
    vals_J: Sequence[int],
    pi_J: Opening1,
    a_J: int | None = None,
    b_J: int | None = None,
) -> PoKSubVProof:
    r"""``PoKSubV'.P(crs, (δ, δ', J), (v_J, π_J)) → π``。

    证明的关系是

    .. math::

        \big(\operatorname{Ver}'(\delta, J, v_J, \pi_J) = 1\big)
        \;\wedge\;
        \big(\operatorname{Ver}'(\delta', J, v_J, \pi_J') = 1\big)

    也就是「``δ'`` 承诺的正是 ``δ`` 在 ``J`` 上的子向量」。

    相比 §6 的原版 ``PoKSubV`` 有两处调整（论文 §8.1 明确说明）：

    1. **CRS 只用 ``crs``**，不需要两个 ``crsn``。因为 ``J = {1, …, n'}``
       时 :math:`u_J = u_{n'}` 完全由 ``crs`` 决定，:math:`U_{n'}`
       不需要从 ``crsn'`` 里取；
    2. **不检查 ``PoProd2``** —— ``Com'`` 的承诺里没有它。

    :param a_J, b_J: 可选的 ``PartndPrimeProd(J, F_J)`` 结果；
                     调用方若已经算过就直接传进来，省一次连乘。
    """
    if a_J is None or b_J is None:
        a_J, b_J = partnd_prime_prod(
            crs.primegen, J, [int(v) for v in vals_J], 1
        )[0]
    u_J = a_J * b_J
    t = _poksubv_prime_transcript(crs, delta, delta_p, J)
    return poksubv_prove(
        N=crs.N,
        g=crs.g,
        g0=crs.g0,
        g1=crs.g1,
        A=delta.A,
        B=delta.B,
        Ap=delta_p.A,
        Bp=delta_p.B,
        Un_old=_NO_U_N,
        Un_new=pow(crs.g, u_J, crs.N),
        Gamma_I=pi_J.Gamma[0],
        Delta_I=pi_J.Delta[0],
        a_I=a_J,
        b_I=b_J,
        transcript=t,
        lambda_bits=crs.lambda_bits,
    )


def poksubv_prime_verify(
    crs: CRS1,
    delta: Digest1,
    delta_p: Digest1,
    J: Sequence[int],
    proof: PoKSubVProof,
) -> bool:
    """``PoKSubV'.V(crs, (δ, δ', J), π) → b``。

    验证方自己重算 :math:`U_{n'} = g^{u_{n'}}`（``n' = |J|``，``J`` 必须是前缀），
    所以证明方没法拿一个假的锚点糊弄过去 —— 这正是把 ``v_J`` 与 ``δ'``
    的长度绑死的那一步。
    """
    J = as_index_set(J)
    if not J or not is_prefix(J):
        return False
    if not (0 <= J[-1] < delta.n):
        return False
    if len(J) != delta_p.n:
        return False

    u_J = product_tree([crs.primegen.get(i) for i in J])
    t = _poksubv_prime_transcript(crs, delta, delta_p, J)
    return poksubv_verify(
        N=crs.N,
        g=crs.g,
        g0=crs.g0,
        g1=crs.g1,
        A=delta.A,
        B=delta.B,
        Ap=delta_p.A,
        Bp=delta_p.B,
        Un_old=_NO_U_N,
        Un_new=pow(crs.g, u_J, crs.N),
        proof=proof,
        transcript=t,
        lambda_bits=crs.lambda_bits,
    )


# ---------------------------------------------------------------------------
# 更新的数据容器
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CreateWitness:
    """``Υ_J = (δ', π_PoKSubV')`` —— ``CreateFrom`` 产出的派生证明。"""

    delta: Digest1
    proof: PoKSubVProof

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"CreateWitness({self.delta!r})"


@dataclass(frozen=True)
class UpdateOp1:
    """``∆`` —— 一次更新操作的内容。

    :param op: ``"mod"`` / ``"add"`` / ``"del"``
    :param K: 被改动的下标集合。``add`` 时必须是 ``{n+1, …, n+|K|}``，
              ``del`` 时必须是 ``{n-|K|+1, …, n}``
    :param F_new: ``mod`` / ``add`` 的**新**值；``del`` 留空
    """

    op: str
    K: tuple[int, ...]
    F_new: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "K", tuple(as_index_set(self.K)))
        object.__setattr__(self, "F_new", tuple(int(v) for v in self.F_new))
        if self.op not in ("mod", "add", "del"):
            raise ValueError(f"未知的 op {self.op!r}")
        if not self.K:
            raise ValueError("更新至少要涉及一个下标")
        if self.op in ("mod", "add") and len(self.F_new) != len(self.K):
            raise ValueError("mod / add 要求 F_new 的长度与 K 一致")
        if self.op == "del" and self.F_new:
            raise ValueError("del 不接受 F_new")

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"UpdateOp1({self.op!r}, K={list(self.K)})"


@dataclass(frozen=True)
class PushedUpdate1:
    """``StrgNode.PushUpdate`` 的输出 ``(δ', n', st', J, F'_J, Υ_∆)``。

    :param delta: 新摘要
    :param st: 发布者的新本地状态
    :param J: 发布者更新后的下标集合
    :param F_J: ``J`` 上的值
    :param F_K: ``Υ_∆`` 里的旧值（``mod`` / ``del`` 有，``add`` 为空）
    :param pi_K: ``Υ_∆`` 里的证据（``mod`` / ``del`` 有，``add`` 为 ``None``）
    """

    delta: Digest1
    st: Opening1
    J: tuple[int, ...]
    F_J: tuple[int, ...]
    F_K: tuple[int, ...] = ()
    pi_K: Opening1 | None = None

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"PushedUpdate1({self.delta!r}, |J|={len(self.J)}, "
            f"|F_K|={len(self.F_K)})"
        )


@dataclass(frozen=True)
class AppliedUpdate1:
    """``StrgNode.ApplyUpdate`` 的输出 ``(b, δ', n', st', J, F'_J)``。

    ``ok`` 为假时 ``delta`` / ``st`` 可能是 ``None``，``reason`` 说明原因。
    """

    ok: bool
    delta: Digest1 | None
    st: Opening1 | None
    J: tuple[int, ...] = ()
    F_J: tuple[int, ...] = ()
    reason: str = ""

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"AppliedUpdate1(ok={self.ok}, reason={self.reason!r})"


# ---------------------------------------------------------------------------
# 内部小工具
# ---------------------------------------------------------------------------

def _partnd(crs: CRS1, I: Sequence[int], vals: Sequence[int]) -> tuple[int, int]:
    """``PartndPrimeProd`` 在 ``k = 1`` 下的单分量取值。"""
    return partnd_prime_prod(crs.primegen, I, [int(v) for v in vals], 1)[0]


def _trick(x: int, y: int, u: int, v: int, N: int, what: str) -> int:
    """``ShamirTrick`` 的包装：失败时抛出可定位的异常。"""
    out = shamir_trick(x, y, u, v, N)
    if out is None:
        raise ValueError(
            f"ShamirTrick 失败（{what}）：两个根不同源，或 gcd(u, v) ≠ 1 —— "
            f"后者几乎总是 PrimeGen 出现碰撞"
        )
    return out


def _replace(
    I: Sequence[int], F_I: Sequence[int], K: Sequence[int], F_K: Sequence[int]
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """把 ``F_I`` 在 ``K`` 上的分量替换成 ``F_K``。"""
    newmap = dict(zip(as_index_set(K), F_K))
    F_new = tuple(newmap.get(i, F_I[pos]) for pos, i in enumerate(I))
    return tuple(I), F_new


def _head_range(n: int, size: int) -> list[int]:
    """``{n, …, n + size - 1}`` —— ``add`` 允许的下标形态（0 基）。"""
    return list(range(n, n + size))


def _tail_range(n: int, size: int) -> list[int]:
    """``{n - size, …, n - 1}`` —— ``del`` 允许的下标形态（0 基）。"""
    return list(range(n - size, n))


# ---------------------------------------------------------------------------
# 会话：Bootstrap
# ---------------------------------------------------------------------------

class VDS1Session:
    """一次 ``VDS1`` 会话：持有公开参数 ``pp = crs`` 与素数映射。

    :param n_max: 文件最多分成多少块。素数 :math:`p_1..p_{n_{max}}` 必须固定，
                  这是隐藏阶群方案的固有约束
    :param k: 块宽（比特数）。``VDS1`` 建议取 1
    :param lambda_bits: 安全参数 :math:`\\lambda`
    :param modulus_bits: 模数位长，``None`` 时取 ``16·λ``
    :param seed: 随机种子（可复现）
    """

    def __init__(
        self,
        n_max: int,
        k: int = 1,
        lambda_bits: int = 128,
        modulus_bits: int | None = None,
        seed: bytes | str = b"vds-v1",
        primegen_cls: type[PrimeGen] | type[PrimeGenHash] = PrimeGen,
        prime_bits: int | None = None,
    ) -> None:
        self.n_max = n_max
        self.k = k
        self.rng = DeterministicRNG(seed)
        self.crs: CRS1 = setup1(
            lambda_bits=lambda_bits,
            k=k,
            n=n_max,
            rng=self.rng,
            modulus_bits=modulus_bits,
            primegen_cls=primegen_cls,
            prime_bits=prime_bits,
        )
        # u_{n'} 只依赖 n'，缓存起来免得每次 PoKSubV' 都重算连乘
        self._u_cache: dict[int, int] = {}
        self._U_cache: dict[int, int] = {}

    # -- 定点累加器 -------------------------------------------------------

    def u_of_prefix(self, n: int) -> int:
        """``u_{n} = p_0·p_1···p_{n-1}``，与 :func:`~svc.yinyan.specialize1` 一致。"""
        if n not in self._u_cache:
            self._u_cache[n] = product_tree(
                [self.crs.primegen.get(i) for i in range(n)]
            )
        return self._u_cache[n]

    def U_of_prefix(self, n: int) -> int:
        """``U_{n} = g^{u_n}``，即 ``VC.Specialize(crs, n)`` 的那个累加器。

        ``VDS1`` 不需要把 :math:`U_n` 放进摘要（§8.2 才需要），
        但 ``PoKSubV'`` 的验证方要用到 :math:`U_{n'}`，这里按需现算并缓存。
        """
        if n not in self._U_cache:
            self._U_cache[n] = pow(self.crs.g, self.u_of_prefix(n), self.crs.N)
        return self._U_cache[n]

    # -- Bootstrap --------------------------------------------------------

    def bootstrap(self) -> tuple[Digest1, Opening1]:
        r"""``Bootstrap(λ) → (δ0, n0, st0)``。

        论文原文：``Set n0 ← 0, δ0 ← ((g0, g1), n0) and st0 ← (g0, g1)``。

        注意 :math:`\delta_0` 与 ``Com'`` 作用在空向量上的结果一致：
        空集的两个划分都是空集，两个素数连乘都是 1，
        于是 :math:`(g_0^1, g_1^1)`。而 :math:`st_0 = (g_0, g_1)` 恰好是
        「下标集合为空」时那份打开证明，因此 ``Ver'`` 在 ``I = ∅`` 上通过。
        """
        return (
            Digest1(A=self.crs.g0, B=self.crs.g1, n=0),
            Opening1(Gamma=(self.crs.g0,), Delta=(self.crs.g1,), I=()),
        )

    def commit(self, vals: Sequence[int]) -> tuple[Digest1, Opening1]:
        """把一整个向量提交，并给出根打开证明 ``π_{[n]}``。

        ``π_{[n]}`` 的补集为空，所以两个分量都是 ``(g0, g1)`` ——
        与 ``st0`` 同形。任何子集的打开都可以由它 disaggregate 出来。
        """
        delta = com_prime(self.crs, vals)
        n = len(vals)
        # 根打开 π_[n] 的补集是空集，两个分量都是 (g0, g1)
        st = Opening1(
            Gamma=(self.crs.g0,),
            Delta=(self.crs.g1,),
            I=tuple(range(n)),
        )
        return delta, st

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"VDS1Session(n_max={self.n_max}, k={self.k}, "
            f"|N|={self.crs.N.bit_length()})"
        )


# ---------------------------------------------------------------------------
# 存储节点
# ---------------------------------------------------------------------------

class StorageNode1:
    """一个 ``VDS1`` 存储节点，持有文件的一部分 ``(I, F_I)`` 与证据 ``π_I``。"""

    def __init__(self, node_id: str, session: VDS1Session, view: LocalView1):
        self.node_id = node_id
        self.session = session
        self.view = view

    # -- 只读属性 ---------------------------------------------------------

    @property
    def crs(self) -> CRS1:
        return self.session.crs

    @property
    def I(self) -> tuple[int, ...]:
        return self.view.I

    @property
    def FI(self) -> tuple[int, ...]:
        return self.view.FI

    @property
    def st(self) -> Opening1:
        return self.view.st

    @property
    def delta(self) -> Digest1:
        return self.view.delta

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"StorageNode1({self.node_id!r}, {self.view!r})"

    def _with(
        self, delta: Digest1, st: Opening1, I: Sequence[int], F_I: Sequence[int]
    ) -> "StorageNode1":
        I = tuple(as_index_set(I))
        return StorageNode1(
            self.node_id, self.session, LocalView1(delta, st, I, tuple(F_I))
        )

    # -- 正确性检查 -------------------------------------------------------

    def check_local_view(self) -> bool:
        r"""检查本节点是否真持有它声称的那部分数据。

        判据就是 :func:`ver_prime`（论文 §8.1 证明里的
        :math:`st_1^{a_I} = \delta_1 \wedge st_2^{b_I} = \delta_2`）。
        """
        return ver_prime(
            self.crs, self.delta, list(self.I), list(self.FI), self.st
        )

    # -- StrgNode.AddStorage ---------------------------------------------

    def add_storage(self, other: "StorageNode1") -> "StorageNode1":
        """``StrgNode.AddStorage(δ, n, st, I, F_I, Q, F_Q, π_Q) → (st', J, F_J)``。

        论文原文在 ``I = ∅`` 时把 ``st'`` 直接置为 ``π_Q``；
        两种情形其实可以由同一个公式给出（空集的 ``π_∅`` 就是 ``(g0, g1)``，
        ``Agg(π_∅, π_Q)`` 等于 ``π_Q``），这里统一走 :func:`agg_prime`。
        """
        if self.view.delta != other.view.delta:
            raise ValueError("两个节点的摘要不同，不能合并")
        if set(self.I) & set(other.I):
            raise ValueError("AddStorage 要求两份存储不相交")

        if not self.I:
            st = other.st
        else:
            st = agg_prime(
                self.crs,
                list(self.I), list(self.FI), self.st,
                list(other.I), list(other.FI), other.st,
            )

        valmap = dict(zip(self.I, self.FI))
        valmap.update(dict(zip(other.I, other.FI)))
        J = as_index_set(list(self.I) + list(other.I))
        return self._with(self.delta, st, J, [valmap[i] for i in J])

    # -- StrgNode.RmvStorage ---------------------------------------------

    def rmv_storage(self, K: Sequence[int]) -> "StorageNode1":
        """``StrgNode.RmvStorage(δ, n, st, I, F_I, K) → (st', J, F_J)``。

        ``J = I \\ K``，``π_J ← VC.Disagg'(crs, I, F_I, π_I, J)``。
        """
        K = as_index_set(K)
        if not set(K) <= set(self.I):
            raise ValueError("要删除的下标必须都在本地集合里")
        J = [i for i in self.I if i not in set(K)]
        if not J:
            raise ValueError("删除后什么都不剩了，节点应直接下线")
        st = disagg_prime(self.crs, list(self.I), list(self.FI), self.st, J)
        return self._with(self.delta, st, J, [self.view.value_of(i) for i in J])

    # -- StrgNode.Retrieve -----------------------------------------------

    def retrieve(self, Q: Sequence[int]) -> tuple[tuple[int, ...], Opening1]:
        """``StrgNode.Retrieve(δ, n, st, I, F_I, Q) → (F_Q, π_Q)``。

        ``π_Q ← VC.Disagg'(crs, I, F_I, st, Q)`` —— 一次拆分，
        代价只与 ``|I \\ Q|`` 有关，节点不需要为每个可能的 ``Q`` 预存证明。
        """
        Q = as_index_set(Q)
        if not set(Q) <= set(self.I):
            missing = sorted(set(Q) - set(self.I))
            raise ValueError(f"本节点不持有下标 {missing}，无法满足检索请求")
        pi_Q = disagg_prime(self.crs, list(self.I), list(self.FI), self.st, Q)
        return tuple(self.view.value_of(i) for i in Q), pi_Q

    def has(self, Q: Sequence[int]) -> bool:
        """是否持有 ``Q`` 的全部下标。"""
        return self.view.has(Q)

    # -- StrgNode.CreateFrom ---------------------------------------------

    def create_from(
        self, J: Sequence[int]
    ) -> tuple["StorageNode1", CreateWitness]:
        """``StrgNode.CreateFrom(δ, n, st, I, F_I, J) → (δ', n', st', J, F_J, Υ_J)``。

        从手里的大文件里派生出一个新文件 ``F_J``：

        .. code-block:: text

            δ'  ← VC.Com'(crs, F_J)
            n'  ← |J|
            st' ← J 在 δ' 下的打开 = (g0, g1)      （因为 J = [n']）
            Υ_J ← (δ', PoKSubV'.P(crs, (δ, δ', J), (F_J, Disagg'(π_I, J))))

        新文件**不需要重新分发**：``Υ_J`` 是常数大小（几个群元素 + 三个标量），
        客户端跑一次 :meth:`ClientNode1.get_create` 就能确认
        「``δ'`` 承诺的确实是原文件在 ``J`` 上的那段」。

        论文 ``GetCreate`` 会检查 ``J = {1, …, |J|}``，所以 ``J`` 必须是前缀 ——
        这对应「``C'`` 也应该是一个向量承诺，其打开必须是一个正常向量
        而非一般子向量」这条要求。
        """
        J = as_index_set(J)
        if not J:
            raise ValueError("J 不能为空")
        if not set(J) <= set(self.I):
            raise ValueError("CreateFrom 要求 J ⊆ I")
        if not is_prefix(J):
            raise ValueError(
                f"J = {list(J)} 不是 {{0, …, |J|-1}}；"
                f"PoKSubV' 要求子向量是前缀，否则 u_J ≠ u_{{|J|}}"
            )

        F_J = tuple(self.view.value_of(i) for i in J)
        delta_p = com_prime(self.crs, F_J)

        # PoKSubV' 的见证是「J 在**旧**摘要 δ 下的打开」，也就是 Disagg'(π_I, J)
        pi_J_old = disagg_prime(
            self.crs, list(self.I), list(self.FI), self.st, J
        )
        proof = poksubv_prime_prove(
            self.crs, self.delta, delta_p, J, F_J, pi_J_old
        )

        # 派生子节点的本地状态必须是「J 在**新**摘要 δ' 下的打开」。
        # 因为 J 被要求是前缀（即新文件的全部下标），这份打开就是根打开
        # (g0, g1) —— 与 Bootstrap 的 st0 同形。
        #
        # 论文正文这里写的是 st' ← VC.Disagg(pp, I, F_I, π_I, J)，那算出来的是
        # 「J 在旧摘要 δ 下的打开」g0^{a_L}，它满足 Ver'(δ, J, F_J, ·) 但**不**
        # 满足 Ver'(δ', J, F_J, ·)：那是 a_L = 1 时才碰巧成立的特例。
        # 论文自己的正确性证明要求 (pp, δ', n', st', J, F_J) 是合法本地视图
        # （"validity ... comes from correctness of VC.Com'"），
        # 所以这里按证明的要求取新摘要下的打开。
        st_p = Opening1(
            Gamma=(self.crs.g0,), Delta=(self.crs.g1,), I=J
        )
        derived = self._with(delta_p, st_p, J, F_J)
        return derived, CreateWitness(delta=delta_p, proof=proof)

    # -- StrgNode.PushUpdate ---------------------------------------------

    def push_update(self, op: UpdateOp1) -> PushedUpdate1:
        r"""``StrgNode.PushUpdate(δ, n, st, I, F_I, op, ∆) → (δ', n', st', J, F'_J, Υ_∆)``。

        三种操作的核心差别在于**新摘要从哪来**：

        * ``mod``：新摘要的两个分量直接就是 ``π_K`` 提到新指数上 ——
          :math:`\delta' = ((\Gamma_K^{a'_K}, \Delta_K^{b'_K}), n)`；
        * ``add``：把旧摘要抬到新增位置的指数上 ——
          :math:`\delta' = ((A^{a'_K}, B^{b'_K}), n + |K|)`；
        * ``del``：新摘要就是 ``π_K`` 本身 ——
          :math:`\delta' = ((\Gamma_K, \Delta_K), n - |K|)`。

        三种都能在**不重新遍历整个文件**的前提下算出新摘要，
        这正是 VDS 允许「只知道一部分数据的节点也能发布更新」的原因。
        """
        crs, N = self.crs, self.crs.N
        delta, I, F_I, st = self.delta, self.I, self.FI, self.st
        K, F_new = op.K, op.F_new
        n = delta.n

        if op.op == "add":
            if list(K) != _head_range(n, len(K)):
                raise ValueError(
                    f"add 要求 K = {_head_range(n, len(K))}（追加到文件尾部），"
                    f"收到 {list(K)}"
                )
            a_K, b_K = _partnd(crs, K, F_new)
            delta_p = Digest1(
                A=pow(delta.A, a_K, N), B=pow(delta.B, b_K, N), n=n + len(K)
            )
            valmap = dict(zip(I, F_I))
            valmap.update(zip(K, F_new))
            J = as_index_set(list(I) + list(K))
            F_J = tuple(valmap[i] for i in J)
            # 发布者的本地状态**不变**：J = I ∪ K 时
            # Γ_J = g0^{a·a'_K / (a_I·a'_K)} = Γ_I
            # 新增位置带来的指数因子在分子分母里同时出现，约掉了
            st_p = Opening1(Gamma=st.Gamma, Delta=st.Delta, I=J)
            return PushedUpdate1(
                delta=delta_p, st=st_p, J=J, F_J=F_J, F_K=(), pi_K=None
            )

        if op.op == "mod":
            if not set(K) <= set(I):
                raise ValueError("mod 要求发布者持有 K 中的全部下标")
            F_K = tuple(self.view.value_of(i) for i in K)
            pi_K = disagg_prime(crs, list(I), list(F_I), st, K)
            a_K, b_K = _partnd(crs, K, F_new)
            delta_p = Digest1(
                A=pow(pi_K.Gamma[0], a_K, N),
                B=pow(pi_K.Delta[0], b_K, N),
                n=n,
            )
            J, F_J = _replace(I, F_I, K, F_new)
            # 本地状态不变：mod 的 K ⊆ I，Γ_I = g0^{a/a_I} 在指数上下
            # a/a_K·a'_K 与 a_I/a_K·a'_K 同时出现，约掉后恒等
            return PushedUpdate1(
                delta=delta_p, st=st, J=J, F_J=F_J, F_K=F_K, pi_K=pi_K
            )

        # op == "del"
        if not set(K) <= set(I):
            raise ValueError("del 要求发布者持有 K 中的全部下标")
        F_K = tuple(self.view.value_of(i) for i in K)
        pi_K = disagg_prime(crs, list(I), list(F_I), st, K)
        delta_p = Digest1(A=pi_K.Gamma[0], B=pi_K.Delta[0], n=n - len(K))
        J = tuple(i for i in I if i not in set(K))
        # 本地状态也不变：Γ_{I\K} = g0^{(a/a_K)/(a_I/a_K)} = g0^{a/a_I} = Γ_I
        st_p = Opening1(Gamma=st.Gamma, Delta=st.Delta, I=J)
        return PushedUpdate1(
            delta=delta_p, st=st_p, J=J,
            F_J=tuple(self.view.value_of(i) for i in J),
            F_K=F_K, pi_K=pi_K,
        )

    # -- StrgNode.ApplyUpdate --------------------------------------------

    def apply_update(
        self, op: UpdateOp1, pushed: PushedUpdate1
    ) -> AppliedUpdate1:
        r"""``StrgNode.ApplyUpdate(δ, n, st, I, F_I, op, ∆, Υ_∆) → (b, δ', n', st', J, F'_J)``。

        应用方**看不到** ``∆`` 里 K 上的新内容以外的东西，
        也看不到 ``δ'``（它自己按同样的公式算出来，再和发布方的对比即可）。

        ``mod`` / ``del`` 的本地状态更新分三种情形（论文原文）：

        * :math:`I \cap K = \emptyset`：两份状态做一次 ``ShamirTrick``，
          得到 :math:`g_0^{a/(a_I a_K)}`（``mod`` 再抬到 :math:`a'_K`)；
        * :math:`I \cap K = K`：状态**不变**。因为 :math:`K \subseteq I` 时
          新值造成的因子在 :math:`a/a_I` 里被约掉了；
        * 其余情形（:math:`L = I \cap K \notin \{K, \emptyset\}`）：
          把 ``K`` 拆成 ``L ⊔ L̄``。``L`` 那半边不改变状态，
          只需对 ``L̄`` 做一次 ``ShamirTrick``。
        """
        crs, N = self.crs, self.crs.N
        delta, I, F_I, st = self.delta, self.I, self.FI, self.st
        n = delta.n
        K = op.K
        F_K = pushed.F_K
        pi_K = pushed.pi_K

        def _accept(
            delta_p: Digest1, st_p: Opening1, J: Sequence[int], F_J: Sequence[int]
        ) -> AppliedUpdate1:
            """把新视图套上去之前先自检一次。

            诚实应用方算出的结果一定通过。这条检查挡的是
            「拿一份陈旧的 ``Υ_∆`` 打在一个已经更新过的摘要上」这类调用 ——
            那时算出来的 ``(δ', st')`` 彼此不匹配，若不设防会把本地视图
            悄悄改成无效状态，之后所有检索都会失败而且查不出原因。
            """
            if not ver_prime(crs, delta_p, list(J), list(F_J), st_p):
                return AppliedUpdate1(
                    False, None, None,
                    reason="套用更新后本地视图校验失败："
                           "Υ_∆ 很可能对应的是另一版摘要",
                )
            return AppliedUpdate1(True, delta_p, st_p, tuple(J), tuple(F_J))

        # ---- op = add ----
        if op.op == "add":
            if list(K) != _head_range(n, len(K)):
                return AppliedUpdate1(
                    False, None, None, reason=(
                        f"add 的下标必须是 {_head_range(n, len(K))}"
                        f"（追加到文件尾部），收到 {list(K)}"
                    ),
                )
            a_K, b_K = _partnd(crs, K, op.F_new)
            delta_p = Digest1(
                A=pow(delta.A, a_K, N), B=pow(delta.B, b_K, N), n=n + len(K)
            )
            st_p = Opening1(
                Gamma=(pow(st.Gamma[0], a_K, N),),
                Delta=(pow(st.Delta[0], b_K, N),),
                I=I,
            )
            return _accept(delta_p, st_p, I, F_I)

        # ---- mod / del：先验 Υ_∆ ----
        if pi_K is None:
            return AppliedUpdate1(
                False, None, None, reason="Υ_∆ 里没有 π_K，无法验更新证据"
            )
        if len(F_K) != len(K):
            return AppliedUpdate1(
                False, None, None, reason="Υ_∆ 里 F_K 的长度与 K 不符"
            )
        if op.op == "del":
            if list(K) != _tail_range(n, len(K)):
                return AppliedUpdate1(
                    False, None, None, reason=(
                        f"del 的下标必须是文件末尾的 {_tail_range(n, len(K))}，"
                        f"收到 {list(K)}"
                    ),
                )
        if not ver_prime(crs, delta, list(K), list(F_K), pi_K):
            return AppliedUpdate1(
                False, None, None,
                reason="VC.Ver'(δ, K, F_K, π_K) 不成立 —— 更新证据与当前摘要不符",
            )

        # ---- 三种情形共用的状态更新 ----
        a_I, b_I = _partnd(crs, I, F_I) if I else (1, 1)
        Gamma_I, Delta_I = st.Gamma[0], st.Delta[0]
        L = [i for i in I if i in set(K)]
        Lbar = [i for i in K if i not in set(L)]

        def _new_state(f_new: Sequence[int] | None) -> tuple[int, int]:
            """按 ``L`` 的三种情形算出新的 ``(Γ'_I, Δ'_I)``。

            :param f_new: ``mod`` 的新值；``del`` 传 ``None``（没有额外抬指数）

            三种情形的共同点是最终都要凑出 :math:`g_0^{a' / a'_I}`，
            而 :math:`a'_I` 只在 ``I`` 内部的部分变了 ——
            所以只需处理 ``K`` 中**落在 ``I`` 之外**的那半个 ``L̄``。
            这也解释了为什么 ``I ∩ K = K`` 时状态完全不动。
            """
            if not I:
                return Gamma_I, Delta_I

            if not L:  # I ∩ K = ∅，L̄ = K
                a_K, b_K = _partnd(crs, K, F_K)
                g = _trick(Gamma_I, pi_K.Gamma[0], a_I, a_K, N, "mod/del Γ")
                d = _trick(Delta_I, pi_K.Delta[0], b_I, b_K, N, "mod/del Δ")
                if f_new is not None:  # mod 还要抬 a'_K
                    a_new, b_new = _partnd(crs, K, f_new)
                    g, d = pow(g, a_new, N), pow(d, b_new, N)
                return g, d

            if len(L) == len(K):  # I ∩ K = K，状态不变
                return Gamma_I, Delta_I

            # L = I ∩ K ∉ {K, ∅}：只对 L̄ = K \ L 做一次 ShamirTrick
            F_Lb = tuple(F_K[K.index(i)] for i in Lbar)
            pi_Lb = disagg_prime(crs, list(K), list(F_K), pi_K, Lbar)
            a_Lb, b_Lb = _partnd(crs, Lbar, F_Lb)
            g = _trick(Gamma_I, pi_Lb.Gamma[0], a_I, a_Lb, N, "mod/del Γ")
            d = _trick(Delta_I, pi_Lb.Delta[0], b_I, b_Lb, N, "mod/del Δ")
            if f_new is not None:
                # 抬的指数必须是 a'_{L̄}（只有 K 落在 I 之外的那部分），
                # 不是整个 a'_K —— 后者会把 I 内部那份重复计入
                F_Lb_new = tuple(f_new[K.index(i)] for i in Lbar)
                a_Lb_new, b_Lb_new = _partnd(crs, Lbar, F_Lb_new)
                g, d = pow(g, a_Lb_new, N), pow(d, b_Lb_new, N)
            return g, d

        if op.op == "mod":
            a_new, b_new = _partnd(crs, K, op.F_new)
            delta_p = Digest1(
                A=pow(pi_K.Gamma[0], a_new, N),
                B=pow(pi_K.Delta[0], b_new, N),
                n=n,
            )
            g, d = _new_state(op.F_new)
            # 新内容只覆盖 K 那一段，其余部分保持不变
            J, F_J = _replace(I, F_I, K, op.F_new)
        else:  # del
            delta_p = Digest1(A=pi_K.Gamma[0], B=pi_K.Delta[0], n=n - len(K))
            g, d = _new_state(None)
            J = [i for i in I if i not in set(K)]
            F_J = tuple(self.view.value_of(i) for i in J)

        st_p = Opening1(Gamma=(g,), Delta=(d,), I=tuple(J))
        return _accept(delta_p, st_p, J, F_J)

    # -- 便捷入口：同时推进本地视图 --------------------------------------

    def commit_update(self, op: UpdateOp1) -> tuple[PushedUpdate1, "StorageNode1"]:
        """``push_update`` 的便捷包装：顺便把本地视图推进到新版本。

        论文里 ``PushUpdate`` 只返回新状态，节点自己再套上去；
        现实实现里这两步总是一起做，这里直接给出来免得调用方漏掉。
        """
        pushed = self.push_update(op)
        return pushed, self._with(pushed.delta, pushed.st, pushed.J, pushed.F_J)


# ---------------------------------------------------------------------------
# 客户端节点
# ---------------------------------------------------------------------------

class ClientNode1:
    r"""一个 ``VDS1`` 客户端节点。它只保存摘要 :math:`\delta`。"""

    def __init__(self, node_id: str, session: VDS1Session, delta: Digest1):
        self.node_id = node_id
        self.session = session
        self.delta = delta

    @property
    def crs(self) -> CRS1:
        return self.session.crs

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"ClientNode1({self.node_id!r}, {self.delta!r})"

    # -- ClntNode.VerRetrieve --------------------------------------------

    def ver_retrieve(
        self, Q: Sequence[int], F_Q: Sequence[int], pi_Q: Opening1
    ) -> bool:
        """``ClntNode.VerRetrieve(δ, Q, F_Q, π_Q) → b``，即 :func:`ver_prime`。"""
        return ver_prime(self.crs, self.delta, Q, F_Q, pi_Q)

    # -- ClntNode.GetCreate ----------------------------------------------

    def get_create(
        self, J: Sequence[int], upsilon_J: CreateWitness
    ) -> tuple[bool, Digest1 | None]:
        r"""``ClntNode.GetCreate(δ, J, Υ_J) → (b, δ')``。

        论文原文：

        .. code-block:: text

            Parse Υ_J := (δ', π_PoKSubV'), set n' = |J| and output
            b ← PoKSubV'.V(crs, (δ, δ', J), π) ∧ J = {1, …, |J|} and δ'.

        客户端在这里做了两件事：

        1. **格式检查** ``J = {1, …, |J|}`` —— 保证新文件确实是一个「向量」，
           ``PoKSubV'`` 结尾那条 :math:`Q_C^\ell g^{r_c} = U_{n'}` 才有意义；
        2. **验证常数大小的证明** ``PoKSubV'.V`` —— 确认派生出的 ``δ'``
           承诺的就是本文件在 ``J`` 上的那段，且长度恰好 ``n'``。

        通过之后客户端就可以把 :math:`\delta` 换成 :math:`\delta'`，
        整个过程不需要传输 ``F_J`` 的内容。

        :returns: ``(b, δ')``；``b`` 为假时第二项是 ``None``
        """
        J = as_index_set(J)
        delta_p = upsilon_J.delta

        if not is_prefix(J):
            return False, None
        if len(J) != delta_p.n:
            return False, None
        if J and J[-1] >= self.delta.n:
            return False, None

        ok = poksubv_prime_verify(
            self.crs, self.delta, delta_p, J, upsilon_J.proof
        )
        return (True, delta_p) if ok else (False, None)

    # -- ClntNode.ApplyUpdate --------------------------------------------

    def apply_update(
        self, op: UpdateOp1, pushed: PushedUpdate1
    ) -> tuple[bool, Digest1 | None]:
        """``ClntNode.ApplyUpdate(δ, op, ∆, Υ_∆) → (b, δ')``。

        与 :meth:`StorageNode1.apply_update` 的前半段完全相同 ——
        客户端只关心「这次更新合不合法」和「新摘要长什么样」，
        不关心任何本地状态。
        """
        crs, N = self.crs, self.crs.N
        delta, n = self.delta, self.delta.n
        K = op.K

        if op.op == "add":
            if list(K) != _head_range(n, len(K)):
                return False, None
            a_K, b_K = _partnd(crs, K, op.F_new)
            return True, Digest1(
                A=pow(delta.A, a_K, N), B=pow(delta.B, b_K, N), n=n + len(K)
            )

        if pushed.pi_K is None or len(pushed.F_K) != len(K):
            return False, None
        if op.op == "del" and list(K) != _tail_range(n, len(K)):
            return False, None
        if not ver_prime(crs, delta, list(K), list(pushed.F_K), pushed.pi_K):
            return False, None

        if op.op == "mod":
            a_K, b_K = _partnd(crs, K, op.F_new)
            return True, Digest1(
                A=pow(pushed.pi_K.Gamma[0], a_K, N),
                B=pow(pushed.pi_K.Delta[0], b_K, N),
                n=n,
            )
        return True, Digest1(
            A=pushed.pi_K.Gamma[0], B=pushed.pi_K.Delta[0], n=n - len(K)
        )

    # -- AggregateCertificates -------------------------------------------

    def aggregate_certificates(
        self, parts: Sequence[tuple[Sequence[int], Sequence[int], Opening1]]
    ) -> Opening1:
        """``AggregateCertificates(δ, (I, F_I, π_I), (J, F_J, π_J)) → π_K``。

        把多份检索证据合并成一个。合并不需要 ``δ`` 参与，
        所以任何节点都能做这件事。
        """
        return agg_many_to_one1(self.crs, list(parts))

    def aggregate_two(
        self,
        I: Sequence[int], F_I: Sequence[int], pi_I: Opening1,
        J: Sequence[int], F_J: Sequence[int], pi_J: Opening1,
    ) -> Opening1:
        """``AggregateCertificates`` 的两份版本（论文给出的签名）。"""
        return agg_prime(self.crs, I, F_I, pi_I, J, F_J, pi_J)
