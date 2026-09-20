"""论文 §5.1 的第一种 SVC —— 阴阳方案（双累加器）。

核心思想
--------
想承诺一个比特向量 :math:`\\vec v \\in \\{0,1\\}^n`，就为**两个划分**各建一个
RSA 累加器：

.. code-block:: text

    S_{=0} := { i ∈ [n] : v_i = 0 }
    S_{=1} := { i ∈ [n] : v_i = 1 }
    A = g_0^{a}   (a = ∏_{i ∈ S_{=0}} p_i)
    B = g_1^{b}   (b = ∏_{i ∈ S_{=1}} p_i)

打开位置 ``i`` 到比特 ``b`` 就给出「``i`` 在 :math:`S_{=b}` 里」的成员见证。
但光有 ``(A, B)`` 不够 —— 敌手可以把同一个 ``i`` 塞进两个累加器，
于是同一个位置能打开到两个相反的比特。所以承诺里还要带一个
:class:`~svc.pok.PoProd2` 证明，说明 ``A`` 与 ``B`` 所代表的集合**构成 [n] 的划分**。

推广到 ``k`` 比特的块
---------------------
每个块 :math:`v_i \\in \\{0,1\\}^k` 就按**比特位**切成 :math:`k` 组划分，
一共 :math:`2k` 个累加器 :math:`A_1, B_1, \\dots, A_k, B_k`，
每个 :math:`j` 上 :math:`a_j \\cdot b_j = u_{[n]}` 恒成立。

与 §5.2 的对比
--------------
========  ==========================  ==========================
          §5.1（本模块）                §5.2（``svc.scheme``）
========  ==========================  ==========================
生成元     三个 `g, g₀, g₁`              一个 `g`
承诺       2k 个群元素 + k 个 PoProd2     1 个群元素
打开       2k 个群元素                   2 个群元素
验证       需要 PoProd2（较贵）           两次等式检查
========  ==========================  ==========================

§5.1 更啰嗦，但正因为承诺是**一对**累加器，才能在它之上做 ``PoKSubV``
（见 :mod:`svc.pok`）—— 那正是整个 ``CreateFrom`` / ``GetCreate`` 的基础。
§5.2 把承诺压成一个群元素，更省，代价是丢了这份代数结构。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence

from .mathbase import shamir_trick
from .pok import (
    PoProd2Proof,
    Transcript,
    poprod2_prove,
    poprod2_verify,
)
from .primegen import PrimeGen, PrimeGenHash
from .rng import DeterministicRNG
from .scheme import DEFAULT_MODULUS_BITS
from .types import as_index_set

__all__ = [
    "CRS1",
    "CRSn1",
    "Commitment1",
    "Opening1",
    "prime_prod",
    "partnd_prime_prod",
    "setup1",
    "specialize1",
    "commit1",
    "open1",
    "ver1",
    "disagg1",
    "agg1",
    "agg_many_to_one1",
]


# ---------------------------------------------------------------------------
# 数据结构
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CRS1:
    """``crs := (G, g, g0, g1, PrimeGen)``，外加块宽 ``k``。"""

    N: int
    g: int
    g0: int
    g1: int
    primegen: PrimeGen | PrimeGenHash
    k: int = 1
    lambda_bits: int = 128

    @property
    def bits(self) -> int:
        return self.N.bit_length()


@dataclass(frozen=True)
class CRSn1:
    """``crsn := (crs, U_n)``；``u_n`` 一并留着免得重算。"""

    crs: CRS1
    U_n: int
    u_n: int
    n: int

    @property
    def N(self) -> int:
        return self.crs.N


@dataclass(frozen=True)
class Commitment1:
    """``C⋆ := ({A_1, B_1, …, A_k, B_k}, {π_prod^(1), …, π_prod^(k)})``。"""

    A: tuple[int, ...]
    B: tuple[int, ...]
    prod: tuple[PoProd2Proof, ...] = ()
    n: int = 0

    def __post_init__(self) -> None:
        if len(self.A) != len(self.B):
            raise ValueError("A 与 B 的个数必须一致")

    @property
    def k(self) -> int:
        return len(self.A)

    def product(self, j: int) -> int:
        """``C_j = A_j · B_j``。"""
        return self.A[j] * self.B[j]


@dataclass(frozen=True)
class Opening1:
    """``π_I := {(Γ_{I,1}, Δ_{I,1}), …, (Γ_{I,k}, Δ_{I,k})}``。"""

    Gamma: tuple[int, ...]
    Delta: tuple[int, ...]
    I: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if len(self.Gamma) != len(self.Delta):
            raise ValueError("Γ 与 Δ 的个数必须一致")
        object.__setattr__(self, "I", as_index_set(self.I))

    @property
    def k(self) -> int:
        return len(self.Gamma)


# ---------------------------------------------------------------------------
# 辅助函数（论文 §5.1 的 PartndPrimeProd 与 PrimeProd）
# ---------------------------------------------------------------------------

def prime_prod(primegen, I: Iterable[int]) -> int:
    """``PrimeProd(I) → u_I := ∏_{i ∈ I} p_i``。"""
    out = 1
    for i in I:
        out *= primegen.get(i)
    return out


def partnd_prime_prod(primegen, I: Sequence[int], vals: Sequence[int], k: int):
    """``PartndPrimeProd(I, y) → ((a_{I,1}, b_{I,1}), …, (a_{I,k}, b_{I,k}))``。

    对每个比特位 :math:`j`，把 ``I`` 按各个值第 :math:`j` 位是 0 还是 1 分成两堆：

    .. code-block:: text

        a_{I,j} = ∏_{l : y_lj = 0} p_{i_l}
        b_{I,j} = ∏_{l : y_lj = 1} p_{i_l}

    恒有 :math:`a_{I,j} \\cdot b_{I,j} = u_I` —— 这是整套方案的关键不变量。
    """
    I = as_index_set(I)
    if len(I) != len(vals):
        raise ValueError(f"I 有 {len(I)} 个位置，但给了 {len(vals)} 个值")
    if k <= 0:
        raise ValueError("块宽 k 必须为正")

    primes = [primegen.get(i) for i in I]
    out: list[tuple[int, int]] = []
    for j in range(k):
        a = b = 1
        for p, v in zip(primes, vals):
            if (int(v) >> j) & 1:
                b *= p
            else:
                a *= p
        out.append((a, b))
    return out


def complement(I: Sequence[int], n: int) -> list[int]:
    """``[n] \\ I``。"""
    s = set(I)
    return [i for i in range(n) if i not in s]


# ---------------------------------------------------------------------------
# VC.Setup / VC.Specialize
# ---------------------------------------------------------------------------

def setup1(
    lambda_bits: int,
    k: int,
    n: int,
    rng: DeterministicRNG | None = None,
    *,
    modulus_bits: int | None = None,
    primegen_cls: type = PrimeGen,
    prime_bits: int | None = None,
) -> CRS1:
    """``VC.Setup(1^λ, {0,1}^k) → crs``。

    生成隐藏阶群并采样三个生成元 ``g, g0, g1``。

    :param prime_bits: 下标素数的位长。默认 ``n.bit_length() + 1``
                       （论文说 ``PrimeGen`` 的输出可以只要 ``α = log n`` 位）。
    """
    from .groups import generate_primes

    if lambda_bits <= 0 or k <= 0 or n <= 0:
        raise ValueError("lambda_bits / k / n 都必须为正")
    if modulus_bits is None:
        modulus_bits = max(DEFAULT_MODULUS_BITS, 16 * lambda_bits)
    if rng is None:
        rng = DeterministicRNG(b"yinyan-setup")

    N, g = generate_primes(rng, modulus_bits)
    g0 = pow(g, 2 + rng.randbelow(1 << 32), N)
    g1 = pow(g, 3 + rng.randbelow(1 << 32), N)

    if prime_bits is None:
        # 下标素数要够 n 个。b 位素数约有 2^b/(b·ln2) 个，
        # 所以 b 取 log2(n) 再加几位的余量。论文说的 α = log n 是渐近说法。
        prime_bits = max(16, n.bit_length() + 2)
    return CRS1(
        N=N, g=g, g0=g0, g1=g1,
        primegen=primegen_cls(max_sz=n, bits=prime_bits),
        k=k, lambda_bits=lambda_bits,
    )


def specialize1(crs: CRS1, n: int) -> CRSn1:
    """``VC.Specialize(crs, n) → crsn = (crs, U_n)``，:math:`U_n = g^{u_n}`。"""
    u_n = prime_prod(crs.primegen, range(n))
    return CRSn1(crs=crs, U_n=pow(crs.g, u_n, crs.N), u_n=u_n, n=n)


# ---------------------------------------------------------------------------
# VC.Com / VC.Open / VC.Ver
# ---------------------------------------------------------------------------

def _commit_body(crs: CRS1, vals: Sequence[int]):
    n = len(vals)
    pairs = partnd_prime_prod(crs.primegen, range(n), vals, crs.k)
    A = tuple(pow(crs.g0, a, crs.N) for a, _ in pairs)
    B = tuple(pow(crs.g1, b, crs.N) for _, b in pairs)
    return A, B, pairs


def commit1(
    crsn: CRSn1,
    vals: Sequence[int],
    *,
    with_prod: bool = True,
    ctx: bytes = b"vc1",
) -> tuple[Commitment1, tuple[int, ...]]:
    """``VC.Com*(crsn, v) → (C⋆, aux⋆)``。

    :param with_prod: 是否附上 ``PoProd2`` 证明。
                      §5.1 的完整方案要（`True`）；
                      §8.1 的 ``VC.Com'`` 不要（`False`）——
                      第一种 VDS 用的是那个简化版。
    """
    crs = crsn.crs
    vals = tuple(int(v) for v in vals)
    if not vals:
        raise ValueError("向量不能为空")
    for v in vals:
        if v < 0 or v >= (1 << crs.k):
            raise ValueError(f"值 {v} 超出 k = {crs.k} 位的范围")

    A, B, pairs = _commit_body(crs, vals)

    prod: tuple[PoProd2Proof, ...] = ()
    if with_prod:
        from .pok import PoProd2CRS

        pcrs = PoProd2CRS(N=crs.N, g1=crs.g0, g2=crs.g1, g3=crs.g,
                          lambda_bits=crs.lambda_bits)
        proofs = []
        for j, (a_j, b_j) in enumerate(pairs):
            t = Transcript("poprod2", pcrs.N, pcrs.g1, pcrs.g2, pcrs.g3, ctx, j)
            proofs.append(
                poprod2_prove(pcrs, A[j] * B[j] % crs.N, crsn.U_n, a_j, b_j, t)
            )
        prod = tuple(proofs)

    return Commitment1(A=A, B=B, prod=prod, n=len(vals)), vals


def open1(
    crs: CRS1,
    I: Sequence[int],
    vals_I: Sequence[int],
    aux: Sequence[int],
    *,
    ctx: bytes = b"vc1",
) -> Opening1:
    """``VC.Open*(crsn, I, y, aux⋆) → π_I``。

    先算补集 ``J = [n] \\ I`` 的划分，再把底数抬到对应的指数上：

    .. code-block:: text

        Γ_{I,j} = g_0^{a_{J,j}}      Δ_{I,j} = g_1^{b_{J,j}}

    因为 :math:`a_{J,j} = a_j / a_{I,j}`（``J`` 与 ``I`` 是不相交的两堆），
    所以 :math:`\\Gamma_{I,j}` 恰好是「``I`` 中第 j 位为 0 的那些位置」
    在 :math:`A_j` 里的成员见证。
    """
    I = as_index_set(I)
    n = len(aux)
    if I and I[-1] >= n:
        raise ValueError(f"下标 {I[-1]} 越界（长度 {n}）")
    if len(vals_I) != len(I):
        raise ValueError("vals_I 的长度必须与 I 一致")

    J = complement(I, n)
    vals_J = [int(aux[i]) for i in J]
    pairs = partnd_prime_prod(crs.primegen, J, vals_J, crs.k)

    Gamma = tuple(pow(crs.g0, a, crs.N) for a, _ in pairs)
    Delta = tuple(pow(crs.g1, b, crs.N) for _, b in pairs)
    return Opening1(Gamma=Gamma, Delta=Delta, I=I)


def ver1(
    crsn: CRSn1,
    C: Commitment1,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi: Opening1,
    *,
    check_prod: bool = True,
    ctx: bytes = b"vc1",
) -> bool:
    """``VC.Ver*(crsn, C⋆, I, y, π_I) → b``。

    .. code-block:: text

        b_acc  ← ⋀_j ( Γ_{I,j}^{a_{I,j}} = A_j  ∧  Δ_{I,j}^{b_{I,j}} = B_j )
        b_prod ← ⋀_j PoProd2.V(crs, (A_j·B_j, U_n), π_prod^(j))
        return b_acc ∧ b_prod

    :param check_prod: ``VC.Ver'``（§8.1 用的简化版）传 ``False``
                       —— 那个版本的承诺不带 ``PoProd2``。
    """
    crs = crsn.crs
    I = as_index_set(I)

    if C.k != crs.k:
        return False
    if I and (I[0] < 0 or I[-1] >= C.n):
        return False
    if len(vals_I) != len(I) or pi.k != crs.k:
        return False
    if pi.I and pi.I != I:
        return False

    pairs_I = partnd_prime_prod(crs.primegen, I, [int(v) for v in vals_I], crs.k)

    # ---- b_acc ----
    for j in range(crs.k):
        a_IJ, b_IJ = pairs_I[j]
        if pow(pi.Gamma[j], a_IJ, crs.N) != C.A[j] % crs.N:
            return False
        if pow(pi.Delta[j], b_IJ, crs.N) != C.B[j] % crs.N:
            return False

    # ---- b_prod ----
    if check_prod:
        from .pok import PoProd2CRS

        pcrs = PoProd2CRS(N=crs.N, g1=crs.g0, g2=crs.g1, g3=crs.g,
                          lambda_bits=crs.lambda_bits)
        if len(C.prod) != crs.k:
            return False
        for j in range(crs.k):
            t = Transcript("poprod2", pcrs.N, pcrs.g1, pcrs.g2, pcrs.g3, ctx, j)
            if not poprod2_verify(
                pcrs, C.A[j] * C.B[j] % crs.N, crsn.U_n, C.prod[j], t
            ):
                return False

    return True


# ---------------------------------------------------------------------------
# 增量聚合 / 拆分
# ---------------------------------------------------------------------------

def disagg1(
    crs: CRS1,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening1,
    K: Sequence[int],
) -> Opening1:
    """``VC.Disagg(crs, I, v_I, π_I, K) → π_K``，要求 ``K ⊆ I``。

    .. code-block:: text

        L := I \\ K
        (a_{L,j}, b_{L,j}) ← PartndPrimeProd(L, v_L)
        Γ_{K,j} ← Γ_{I,j}^{a_{L,j}}      Δ_{K,j} ← Δ_{I,j}^{b_{L,j}}

    正确性：:math:`a_{I,j} = a_{L,j} \\cdot a_{K,j}`，所以
    :math:`A_j = \\Gamma_{I,j}^{a_{I,j}} = \\Gamma_{K,j}^{a_{K,j}}`。
    """
    I = as_index_set(I)
    K = as_index_set(K)
    if not set(K) <= set(I):
        raise ValueError("disagg 要求 K ⊆ I")

    L = [i for i in I if i not in set(K)]
    pos = {i: k_ for k_, i in enumerate(I)}
    vals_L = [int(vals_I[pos[i]]) for i in L]

    pairs = partnd_prime_prod(crs.primegen, L, vals_L, crs.k)
    Gamma = tuple(pow(pi_I.Gamma[j], a, crs.N) for j, (a, _) in enumerate(pairs))
    Delta = tuple(pow(pi_I.Delta[j], b, crs.N) for j, (_, b) in enumerate(pairs))
    return Opening1(Gamma=Gamma, Delta=Delta, I=K)


def agg1(
    crs: CRS1,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening1,
    J: Sequence[int],
    vals_J: Sequence[int],
    pi_J: Opening1,
) -> Opening1:
    """``VC.Agg(crs, (I, v_I, π_I), (J, v_J, π_J)) → π_K``，``K = I ∪ J``。

    1. ``L := I ∩ J`` 非空就先把 ``I`` 拆成 ``I \\ L``；
    2. 两份分别算 ``PartndPrimeProd``；
    3. 对应分量各做一次 :func:`~svc.mathbase.shamir_trick`。

    注意本函数**只用通用 ``crs``**，不需要 ``crsn``。
    """
    I = as_index_set(I)
    J = as_index_set(J)
    L = [i for i in I if i in set(J)]
    if L:
        I2 = [i for i in I if i not in set(J)]
        pos = {i: k_ for k_, i in enumerate(I)}
        vals_I2 = [int(vals_I[pos[i]]) for i in I2]
        pi_I2 = disagg1(crs, I, vals_I, pi_I, I2) if I2 else pi_I
    else:
        I2, vals_I2, pi_I2 = I, [int(v) for v in vals_I], pi_I

    pairs_I = partnd_prime_prod(crs.primegen, I2, vals_I2, crs.k)
    pairs_J = partnd_prime_prod(crs.primegen, J, [int(v) for v in vals_J], crs.k)

    Gamma, Delta = [], []
    for j in range(crs.k):
        a_I, b_I = pairs_I[j]
        a_J, b_J = pairs_J[j]

        g_k = shamir_trick(pi_I2.Gamma[j], pi_J.Gamma[j], a_I, a_J, crs.N)
        if g_k is None:
            raise ValueError(
                f"第 {j} 位的 Γ 合并失败：两个根不同源，或 gcd(a_I, a_J) ≠ 1"
                f"（后者通常是 PrimeGen 出现碰撞）"
            )
        d_k = shamir_trick(pi_I2.Delta[j], pi_J.Delta[j], b_I, b_J, crs.N)
        if d_k is None:
            raise ValueError(f"第 {j} 位的 Δ 合并失败：同因")
        Gamma.append(g_k)
        Delta.append(d_k)

    return Opening1(Gamma=tuple(Gamma), Delta=tuple(Delta), I=as_index_set(list(I) + list(J)))


def agg_many_to_one1(crs: CRS1, parts) -> Opening1:
    """把多份证明两两合并成一份（``VC.AggManyToOne``）。

    :param parts: ``[(I, vals_I, π_I), …]``
    """
    cur = [
        (as_index_set(I), tuple(int(v) for v in vals), pi)
        for I, vals, pi in parts
    ]
    if not cur:
        raise ValueError("至少要有一份证明")

    while len(cur) > 1:
        nxt = []
        for t in range(0, len(cur) - 1, 2):
            I1, v1, p1 = cur[t]
            I2, v2, p2 = cur[t + 1]
            merged = agg1(crs, I1, v1, p1, I2, v2, p2)
            # merged.I 是排序后的并集，值必须按同一顺序重摆
            valmap = dict(zip(I1, v1))
            valmap.update(dict(zip(I2, v2)))
            nxt.append((merged.I, tuple(valmap[i] for i in merged.I), merged))
        if len(cur) % 2:
            nxt.append(cur[-1])
        cur = nxt

    return cur[0][2]
