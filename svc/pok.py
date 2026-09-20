"""论文 §6 的知识论证协议族 —— 用于第一种 SVC（§5.1）。

这一族协议解决的是**通信复杂度**问题：证明「我知道位置集合 I 上的取值」
而不必把取值本身发过去。代价是几个群元素，与 ``|I|`` 无关 ——
所以 ``|I|`` 大的时候才划算。

四个协议
--------
:class:`PoProd2` —— 证明 :math:`Y = g_1^a g_2^b \\wedge C = g_3^{ab}`
    用于证明两个 RSA 累加器所代表的集合构成第三个累加器所代表集合的**划分**。
    论文 Fig. 3。

:class:`PoProdStar` —— 证明 :math:`A = \\Gamma^a \\wedge B = \\Delta^b \\wedge C = g^{ab}`
    与 ``PoProd2`` 的区别是底数 :math:`\\Gamma, \\Delta` 由证明方给定（敌手可选），
    所以要用随机底数 :math:`h` 的 ``PoKE2`` 技巧。论文 Fig. 5 里内联的那段。

:class:`PoKOpen` —— 证明「我知道 ``(y, π_I)`` 且它确实打开了 ``C``」。论文 Fig. 5。

:class:`PoKSubV` —— 证明「``C'`` 承诺的正是 ``C`` 在位置 ``I`` 上的子向量」。
    论文 Fig. 6。这是 ``CreateFrom`` / ``GetCreate`` 的基础。

交互式 → 非交互式
------------------
论文的协议是三步 Σ 协议。这里统一用 **Fiat–Shamir** 转成非交互式：

* 挑战 :math:`\\ell \\leftarrow \\mathsf{Primes}(2\\lambda)` 用哈希到素数，
  即论文说的 :math:`H_{\\text{prime}} : \\{0,1\\}^* \\to \\mathsf{Primes}(2\\lambda)`；
* 随机底数 :math:`h` 从 :math:`g^t` 取（隐藏阶群里没有直接哈希到群元的方法）；
* :math:`\\alpha \\leftarrow [0, 2^\\lambda)` 用哈希取整数。

所有挑战都吸附进一个 :class:`Transcript`，保证**绑定**到完整的语句与前面的消息。

.. warning::

   论文特别指出（脚注 17）：这些协议**非交互**版本需要**双倍长度**的素数
   （:math:`2\\lambda` 位），因为对 :math:`\\lambda` 位素数存在显式的平方根攻击。
   本实现按论文取 ``2 * lambda_bits``。
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from .mathbase import is_probable_prime
from .types import fingerprint

__all__ = [
    "Transcript",
    "hash_to_prime",
    "PoProd2CRS",
    "PoProd2Proof",
    "poprod2_prove",
    "poprod2_verify",
    "PoProdStarProof",
    "poprodstar_prove",
    "poprodstar_verify",
    "PoKOpenProof",
    "pokopen_prove",
    "pokopen_verify",
    "PoKSubVProof",
    "poksubv_prove",
    "poksubv_verify",
    "PoKComSubProof",
    "pokcomsub_prove",
    "pokcomsub_verify",
    "describe",
]


# ---------------------------------------------------------------------------
# 挑战生成（Fiat–Shamir 的哈希侧）
# ---------------------------------------------------------------------------

def _digest(label: str, parts) -> bytes:
    h = hashlib.sha256()
    h.update(label.encode())
    for p in parts:
        if isinstance(p, int):
            h.update(b"\x02" + p.to_bytes((max(p.bit_length(), 1) + 7) // 8, "big"))
        elif isinstance(p, (bytes, bytearray)):
            h.update(b"\x03" + bytes(p))
        elif isinstance(p, (tuple, list)):
            h.update(b"\x04")
            for q in p:
                h.update(b"\x02" + int(q).to_bytes((max(int(q).bit_length(), 1) + 7) // 8, "big"))
        else:
            h.update(b"\x05" + str(p).encode())
    return h.digest()


class Transcript:
    """把「语句 + 前面的消息」吸附在一起，再派生挑战。

    每一步都重新哈希整个累积状态，所以后面的挑战绑定了前面的全部内容 ——
    证明方无法针对某个挑战裁剪自己的消息。
    """

    __slots__ = ("_label", "_state", "_counter")

    def __init__(self, label: str, *parts) -> None:
        self._label = label
        self._state = _digest(label, parts)
        self._counter = 0

    def absorb(self, *parts) -> "Transcript":
        self._state = _digest(self._label, (self._state,) + tuple(parts))
        self._counter = 0
        return self

    def _next_state(self) -> bytes:
        self._counter += 1
        return _digest(self._label, (self._state, self._counter))

    def challenge_prime(self, bits: int) -> int:
        """``Primes(bits)`` —— 哈希到素数，绑定当前转录。"""
        return hash_to_prime(self._next_state(), bits)

    def challenge_int(self, bits: int) -> int:
        """``[0, 2^bits)`` 上的整数。"""
        raw = self._next_state()
        v = int.from_bytes(raw, "big")
        return v % (1 << bits)

    def challenge_group(self, g: int, N: int) -> int:
        """群元素 ``h``。隐藏阶群里取 ``h = g^t``（``t`` 从转录派生）。"""
        return pow(g, self.challenge_int(2 * N.bit_length()), N)

    def hexdigest(self) -> str:
        return self._state.hex()[:16]


def hash_to_prime(data: bytes, bits: int) -> int:
    """``H_prime`` —— 反复哈希直到得到 ``bits`` 位素数。

    论文描述：对 ``(y, i)`` 迭代哈希，是素数就输出。
    这里把 ``i`` 作为计数器拼在输入后面，并强制置最高位以锁定位长。
    """
    if bits < 3:
        raise ValueError("素数位长至少为 3")
    counter = 0
    while True:
        raw = hashlib.sha256(data + counter.to_bytes(8, "big")).digest()
        need = (bits + 7) // 8
        while len(raw) < need:
            raw += hashlib.sha256(raw).digest()
        cand = int.from_bytes(raw[:need], "big")
        cand |= 1 << (bits - 1)
        cand |= 1
        if is_probable_prime(cand):
            return cand
        counter += 1
        if counter > 10_000:
            raise RuntimeError("哈希到素数失败：短时间内没找到素数")


# ---------------------------------------------------------------------------
# PoProd2 —— 两个累加器的并集证明（论文 Fig. 3）
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PoProd2CRS:
    """``crs := (G, g1, g2, g3)``。

    在第一种 SVC 里三者分别对应 ``(g0, g1, g)``：
    ``Y = A_j·B_j = g0^{a_j}·g1^{b_j}``，``C = U_n = g^{u_n}``。
    """

    N: int
    g1: int
    g2: int
    g3: int
    lambda_bits: int = 128

    @property
    def bits(self) -> int:
        return self.N.bit_length()


@dataclass(frozen=True)
class PoProd2Proof:
    """``π := ((Q_Y, Q_C), r_a, r_b)``。"""

    QY: int
    QC: int
    ra: int
    rb: int


def poprod2_prove(
    crs: PoProd2CRS, Y: int, C: int, a: int, b: int, transcript: Transcript
) -> PoProd2Proof:
    """``PoProd2.P`` —— 证明 ``Y = g1^a g2^b`` 且 ``C = g3^{a·b}``。

    :param transcript: 已经吸附了 ``(crs, Y, C)`` 的转录；
                       本函数会再吸附 ``(Y, C, a, b 的承诺形态)`` 后派生 :math:`\\ell`。
    """
    t = transcript.absorb(Y, C)
    ell = t.challenge_prime(2 * crs.lambda_bits)

    qa, ra = divmod(a, ell)
    qb, rb = divmod(b, ell)
    qc, _ = divmod(a * b, ell)

    QY = pow(crs.g1, qa, crs.N) * pow(crs.g2, qb, crs.N) % crs.N
    QC = pow(crs.g3, qc, crs.N)
    return PoProd2Proof(QY=QY, QC=QC, ra=ra, rb=rb)


def poprod2_verify(
    crs: PoProd2CRS, Y: int, C: int, proof: PoProd2Proof, transcript: Transcript
) -> bool:
    """``PoProd2.V`` —— 校验。

    .. code-block:: text

        r_c ← r_a · r_b mod ℓ
        接受 ⟺ r_a, r_b ∈ [ℓ]
              ∧ Q_Y^ℓ · g1^{r_a} · g2^{r_b} = Y
              ∧ Q_C^ℓ · g3^{r_c}          = C
    """
    t = transcript.absorb(Y, C)
    ell = t.challenge_prime(2 * crs.lambda_bits)

    if not (0 <= proof.ra < ell and 0 <= proof.rb < ell):
        return False

    rc = proof.ra * proof.rb % ell
    N = crs.N

    lhs_y = pow(proof.QY, ell, N) * pow(crs.g1, proof.ra, N) % N
    lhs_y = lhs_y * pow(crs.g2, proof.rb, N) % N
    if lhs_y != Y % N:
        return False

    lhs_c = pow(proof.QC, ell, N) * pow(crs.g3, rc, N) % N
    return lhs_c == C % N


# ---------------------------------------------------------------------------
# PoProd* —— 底数由证明方给定的版本（论文 Fig. 5 内联的那段）
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PoProdStarProof:
    """``π := ((Q_A, Q_B, Q_C), r_a, r_b)``，外加提前发送的 ``z = (z_a, z_b)``。"""

    za: int
    zb: int
    QA: int
    QB: int
    QC: int
    ra: int
    rb: int


def poprodstar_prove(
    N: int,
    g: int,
    A: int,
    B: int,
    C: int,
    Gamma: int,
    Delta: int,
    a: int,
    b: int,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> PoProdStarProof:
    """``PoProd*.P`` —— 证明 ``A = Γ^a ∧ B = Δ^b ∧ C = g^{a·b}``。

    与 ``PoProd2`` 的关键差别：底数 :math:`\\Gamma, \\Delta` 是语句的一部分
    （由证明方选定，可能是敌手构造的），所以不能直接用 ``PoKE*``；
    改用 ``PoKE2`` 的做法 —— 先让验证方给一个**随机底数** :math:`h`，
    证明方连 :math:`(h^a, h^b)` 一起发过去。
    """
    t = transcript.absorb(A, B, C, Gamma, Delta)

    # 第一轮：随机底数 h，证明方回 (h^a, h^b)
    h = t.challenge_group(g, N)
    za = pow(h, a, N)
    zb = pow(h, b, N)

    # 第二轮：素数挑战 ℓ 与盲化因子 α
    t2 = t.absorb(za, zb)
    ell = t2.challenge_prime(2 * lambda_bits)
    alpha = t2.challenge_int(lambda_bits)

    qa, ra = divmod(a, ell)
    qb, rb = divmod(b, ell)
    qab, _ = divmod(a * b, ell)

    QA = pow(Gamma, qa, N) * pow(h, alpha * qa, N) % N
    QB = pow(Delta, qb, N) * pow(h, alpha * qb, N) % N
    QC = pow(g, qab, N)

    return PoProdStarProof(za=za, zb=zb, QA=QA, QB=QB, QC=QC, ra=ra, rb=rb)


def poprodstar_verify(
    N: int,
    g: int,
    A: int,
    B: int,
    C: int,
    Gamma: int,
    Delta: int,
    proof: PoProdStarProof,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> bool:
    """``PoProd*.V``。

    .. code-block:: text

        r_c ← r_a · r_b mod ℓ
        接受 ⟺ r_a, r_b ∈ [ℓ]
              ∧ Q_A^ℓ · Γ^{r_a} · h^{α·r_a} = A · z_a^α
              ∧ Q_B^ℓ · Δ^{r_b} · h^{α·r_b} = B · z_b^α
              ∧ Q_C^ℓ · g^{r_c}             = C
    """
    t = transcript.absorb(A, B, C, Gamma, Delta)
    h = t.challenge_group(g, N)
    t2 = t.absorb(proof.za, proof.zb)
    ell = t2.challenge_prime(2 * lambda_bits)
    alpha = t2.challenge_int(lambda_bits)

    if not (0 <= proof.ra < ell and 0 <= proof.rb < ell):
        return False

    rc = proof.ra * proof.rb % ell

    lhs_a = pow(proof.QA, ell, N) * pow(Gamma, proof.ra, N) % N
    lhs_a = lhs_a * pow(h, alpha * proof.ra, N) % N
    if lhs_a != A % N * pow(proof.za, alpha, N) % N:
        return False

    lhs_b = pow(proof.QB, ell, N) * pow(Delta, proof.rb, N) % N
    lhs_b = lhs_b * pow(h, alpha * proof.rb, N) % N
    if lhs_b != B % N * pow(proof.zb, alpha, N) % N:
        return False

    lhs_c = pow(proof.QC, ell, N) * pow(g, rc, N) % N
    return lhs_c == C % N


# ---------------------------------------------------------------------------
# PoKOpen —— 打开证明的知识论证（论文 Fig. 5）
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PoKOpenProof:
    """``π := (Γ_I, Δ_I, π_PoProd*)``。"""

    Gamma_I: int
    Delta_I: int
    prod: PoProdStarProof


def pokopen_prove(
    N: int,
    g: int,
    A: int,
    B: int,
    Gamma_I: int,
    Delta_I: int,
    a_I: int,
    b_I: int,
    u_I: int,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> PoKOpenProof:
    """``PoKOpen.P`` —— 证明「我知道 ``(y, π_I)`` 且它打开了 ``C = (A, B)``」。

    做法：先发 ``π_I = (Γ_I, Δ_I)``，再跑一次 ``PoProd*`` 证明
    :math:`\\Gamma_I^{a_I} = A \\wedge \\Delta_I^{b_I} = B \\wedge U_I = g^{a_I b_I}`，
    其中 :math:`U_I = g^{u_I}` 由验证方自己算（所以它是个可信锚点）。
    """
    UI = pow(g, u_I, N)
    t = transcript.absorb("pokopen", UI, Gamma_I, Delta_I)
    prod = poprodstar_prove(
        N, g, A, B, UI, Gamma_I, Delta_I, a_I, b_I, t, lambda_bits
    )
    return PoKOpenProof(Gamma_I=Gamma_I, Delta_I=Delta_I, prod=prod)


def pokopen_verify(
    N: int,
    g: int,
    A: int,
    B: int,
    u_I: int,
    proof: PoKOpenProof,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> bool:
    """``PoKOpen.V`` —— 校验。

    验证方**自己**算 :math:`U_I = g^{u_I}`（``u_I`` 由下标集合唯一确定），
    所以证明方没法拿一个假的锚点糊弄过去。
    """
    UI = pow(g, u_I, N)
    t = transcript.absorb("pokopen", UI, proof.Gamma_I, proof.Delta_I)
    return poprodstar_verify(
        N, g, A, B, UI, proof.Gamma_I, proof.Delta_I, proof.prod, t, lambda_bits
    )


# ---------------------------------------------------------------------------
# PoKSubV —— 证明 C' 承诺的就是 C 在 I 上的子向量（论文 Fig. 6）
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PoKSubVProof:
    """``π := (Γ_I, Δ_I, (Q_A, Q_B, Q'_A, Q'_B, Q_C), r_a, r_b, z)``。"""

    Gamma_I: int
    Delta_I: int
    za: int
    zb: int
    QA: int
    QB: int
    QpA: int
    QpB: int
    QC: int
    ra: int
    rb: int


def poksubv_prove(
    N: int,
    g: int,
    g0: int,
    g1: int,
    A: int,
    B: int,
    Ap: int,
    Bp: int,
    Un_old: int,
    Un_new: int,
    Gamma_I: int,
    Delta_I: int,
    a_I: int,
    b_I: int,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> PoKSubVProof:
    """``PoKSubV.P`` —— 证明「``(A', B')`` 与 ``(A, B)`` 在 ``I`` 上用同一组 ``(a_I, b_I)``」。

    这是 ``PoKOpen`` 与 ``PoProd`` 的**合取**：

    * ``PoKOpen`` 部分证明 :math:`\\Gamma_I^{a_I} = A \\wedge \\Delta_I^{b_I} = B`
      ——「``v_I`` 是 ``C`` 在 ``I`` 上的子向量」；
    * ``PoProd`` 部分证明 :math:`g_0^{a_I} = A' \\wedge g_1^{b_I} = B'`
      ——「``C'`` 的累加器由同一组 :math:`(a_I, b_I)` 构成」。

    两者共用同一个 :math:`(a_I, b_I)`，所以合起来就证明了
    「``C'`` 承诺的正是 ``v_I``」。末了再加一条
    :math:`Q_C^\\ell g^{r_c} = U_{n'}` 把 ``C'`` 的**长度**也绑上。
    """
    t = transcript.absorb("poksubv", A, B, Ap, Bp, Un_old, Un_new, Gamma_I, Delta_I)

    h = t.challenge_group(g, N)
    za = pow(h, a_I, N)
    zb = pow(h, b_I, N)

    t2 = t.absorb(za, zb)
    ell = t2.challenge_prime(2 * lambda_bits)
    alpha = t2.challenge_int(lambda_bits)

    qa, ra = divmod(a_I, ell)
    qb, rb = divmod(b_I, ell)
    qab, _ = divmod(a_I * b_I, ell)

    QpA = pow(g0, qa, N)
    QpB = pow(g1, qb, N)
    QA = pow(Gamma_I, qa, N) * pow(h, alpha * qa, N) % N
    QB = pow(Delta_I, qb, N) * pow(h, alpha * qb, N) % N
    QC = pow(g, qab, N)

    return PoKSubVProof(
        Gamma_I=Gamma_I, Delta_I=Delta_I, za=za, zb=zb,
        QA=QA, QB=QB, QpA=QpA, QpB=QpB, QC=QC, ra=ra, rb=rb,
    )


def poksubv_verify(
    N: int,
    g: int,
    g0: int,
    g1: int,
    A: int,
    B: int,
    Ap: int,
    Bp: int,
    Un_old: int,
    Un_new: int,
    proof: PoKSubVProof,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> bool:
    """``PoKSubV.V``。

    .. code-block:: text

        r_c ← r_a · r_b mod ℓ
        接受 ⟺ r_a, r_b ∈ [ℓ]
              ∧ Q'_A^ℓ · g_0^{r_a}              = A'      ← C' 的第一个累加器
              ∧ Q'_B^ℓ · g_1^{r_b}              = B'      ← C' 的第二个累加器
              ∧ Q_A^ℓ · Γ_I^{r_a} · h^{α·r_a}   = A · z_a^α
              ∧ Q_B^ℓ · Δ_I^{r_b} · h^{α·r_b}   = B · z_b^α
              ∧ Q_C^ℓ · g^{r_c}                 = U_{n'}  ← 绑住新长度

    注意最后一条用的是 :math:`U_{n'}` —— 也就是 **``C'`` 自己的累加器**，
    这正是把 ``v_I`` 与 ``C'`` 绑死的那一步。
    """
    t = transcript.absorb("poksubv", A, B, Ap, Bp, Un_old, Un_new, proof.Gamma_I, proof.Delta_I)
    h = t.challenge_group(g, N)
    t2 = t.absorb(proof.za, proof.zb)
    ell = t2.challenge_prime(2 * lambda_bits)
    alpha = t2.challenge_int(lambda_bits)

    if not (0 <= proof.ra < ell and 0 <= proof.rb < ell):
        return False

    rc = proof.ra * proof.rb % ell

    lhs = pow(proof.QpA, ell, N) * pow(g0, proof.ra, N) % N
    if lhs != Ap % N:
        return False

    lhs = pow(proof.QpB, ell, N) * pow(g1, proof.rb, N) % N
    if lhs != Bp % N:
        return False

    lhs = pow(proof.QA, ell, N) * pow(proof.Gamma_I, proof.ra, N) % N
    lhs = lhs * pow(h, alpha * proof.ra, N) % N
    if lhs != A % N * pow(proof.za, alpha, N) % N:
        return False

    lhs = pow(proof.QB, ell, N) * pow(proof.Delta_I, proof.rb, N) % N
    lhs = lhs * pow(h, alpha * proof.rb, N) % N
    if lhs != B % N * pow(proof.zb, alpha, N) % N:
        return False

    lhs = pow(proof.QC, ell, N) * pow(g, rc, N) % N
    return lhs == Un_new % N


# ---------------------------------------------------------------------------
# PoKComSub —— 两个承诺共享同一个子向量（论文 §6.3）
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PoKComSubProof:
    """``π := (Γ_{I,1}, Δ_{I,1}, Γ_{I,2}, Δ_{I,2}, z, (Q_{A1}, Q_{B1}, Q_{A2}, Q_{B2}, Q_C), r_a, r_b)``。"""

    Gamma1: int
    Delta1: int
    Gamma2: int
    Delta2: int
    za: int
    zb: int
    QA1: int
    QB1: int
    QA2: int
    QB2: int
    QC: int
    ra: int
    rb: int


def pokcomsub_prove(
    N: int,
    g: int,
    A1: int,
    B1: int,
    A2: int,
    B2: int,
    Gamma1: int,
    Delta1: int,
    Gamma2: int,
    Delta2: int,
    a_I: int,
    b_I: int,
    u_I: int,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> PoKComSubProof:
    """``PoKComSub.P`` —— 证明两个承诺在 ``I`` 上共享同一个子向量。

    论文 §6.3 指出这只要把两次 ``PoKOpen`` **AND 合成**即可，
    但要真的省下来，两次必须共用同一组挑战 :math:`h, \\ell, \\alpha`，
    否则就退化成两个独立证明。所以这里不等同于调用两次 ``PoKOpen``，
    而是把四条底数等式塞进同一个 ``PoProd*``：

    .. code-block:: text

        Γ_1^{a_I} = A_1   ∧   Δ_1^{b_I} = B_1
        Γ_2^{a_I} = A_2   ∧   Δ_2^{b_I} = B_2
        U_I = g^{a_I·b_I}

    :param u_I: ``PrimeProd(I)``；验证方会自己算 :math:`U_I = g^{u_I}`，
                所以它是可信锚点，顺带把两次打开绑到同一个下标集合上。
    """
    C = pow(g, u_I, N)
    t = transcript.absorb(
        "pokcomsub", C, A1, B1, A2, B2, Gamma1, Delta1, Gamma2, Delta2
    )
    h = t.challenge_group(g, N)
    za, zb = pow(h, a_I, N), pow(h, b_I, N)

    t2 = t.absorb(za, zb)
    ell = t2.challenge_prime(2 * lambda_bits)
    alpha = t2.challenge_int(lambda_bits)

    qa, ra = divmod(a_I, ell)
    qb, rb = divmod(b_I, ell)
    qab, _ = divmod(a_I * b_I, ell)

    ha = pow(h, alpha * qa, N)
    hb = pow(h, alpha * qb, N)
    return PoKComSubProof(
        Gamma1=Gamma1, Delta1=Delta1, Gamma2=Gamma2, Delta2=Delta2,
        za=za, zb=zb,
        QA1=pow(Gamma1, qa, N) * ha % N,
        QB1=pow(Delta1, qb, N) * hb % N,
        QA2=pow(Gamma2, qa, N) * ha % N,
        QB2=pow(Delta2, qb, N) * hb % N,
        QC=pow(g, qab, N),
        ra=ra, rb=rb,
    )


def pokcomsub_verify(
    N: int,
    g: int,
    A1: int,
    B1: int,
    A2: int,
    B2: int,
    u_I: int,
    proof: PoKComSubProof,
    transcript: Transcript,
    lambda_bits: int = 128,
) -> bool:
    """``PoKComSub.V``。

    .. code-block:: text

        r_c ← r_a · r_b mod ℓ
        接受 ⟺ r_a, r_b ∈ [ℓ]
              ∧ Q_{A1}^ℓ Γ_1^{r_a} h^{α·r_a} = A_1 z_a^α
              ∧ Q_{B1}^ℓ Δ_1^{r_b} h^{α·r_b} = B_1 z_b^α
              ∧ Q_{A2}^ℓ Γ_2^{r_a} h^{α·r_a} = A_2 z_a^α
              ∧ Q_{B2}^ℓ Δ_2^{r_b} h^{α·r_b} = B_2 z_b^α
              ∧ Q_C^ℓ g^{r_c}               = U_I
    """
    C = pow(g, u_I, N)
    t = transcript.absorb(
        "pokcomsub", C, A1, B1, A2, B2,
        proof.Gamma1, proof.Delta1, proof.Gamma2, proof.Delta2,
    )
    h = t.challenge_group(g, N)
    t2 = t.absorb(proof.za, proof.zb)
    ell = t2.challenge_prime(2 * lambda_bits)
    alpha = t2.challenge_int(lambda_bits)

    if not (0 <= proof.ra < ell and 0 <= proof.rb < ell):
        return False

    def _check(Q: int, base: int, rhs: int, r: int, z: int) -> bool:
        lhs = pow(Q, ell, N) * pow(base, r, N) % N
        lhs = lhs * pow(h, alpha * r, N) % N
        return lhs == rhs % N * pow(z, alpha, N) % N

    if not _check(proof.QA1, proof.Gamma1, A1, proof.ra, proof.za):
        return False
    if not _check(proof.QB1, proof.Delta1, B1, proof.rb, proof.zb):
        return False
    if not _check(proof.QA2, proof.Gamma2, A2, proof.ra, proof.za):
        return False
    if not _check(proof.QB2, proof.Delta2, B2, proof.rb, proof.zb):
        return False

    rc = proof.ra * proof.rb % ell
    return pow(proof.QC, ell, N) * pow(g, rc, N) % N == C % N


def describe(proof) -> str:
    """给演示/日志用的简短指纹。"""
    if isinstance(proof, PoProd2Proof):
        return f"PoProd2(QY={fingerprint(proof.QY)}, QC={fingerprint(proof.QC)})"
    if isinstance(proof, PoProdStarProof):
        return (
            f"PoProd*(z={fingerprint(proof.za)}/{fingerprint(proof.zb)}, "
            f"Q={fingerprint(proof.QA)}/{fingerprint(proof.QB)}/{fingerprint(proof.QC)})"
        )
    if isinstance(proof, PoKOpenProof):
        return f"PoKOpen(Γ={fingerprint(proof.Gamma_I)}, Δ={fingerprint(proof.Delta_I)})"
    if isinstance(proof, PoKSubVProof):
        return (
            f"PoKSubV(Γ={fingerprint(proof.Gamma_I)}, Δ={fingerprint(proof.Delta_I)}, "
            f"Q′=({fingerprint(proof.QpA)},{fingerprint(proof.QpB)}))"
        )
    if isinstance(proof, PoKComSubProof):
        return (
            f"PoKComSub(Γ=({fingerprint(proof.Gamma1)},{fingerprint(proof.Gamma2)}), "
            f"Q=({fingerprint(proof.QA1)},{fingerprint(proof.QB1)}))"
        )
    return repr(proof)
