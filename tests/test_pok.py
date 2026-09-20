"""论文 §6 的知识论证（AoK）测试。

四个协议，每个都验两头：

* **诚实通过** —— 用真实见证生成的证明必须被接受；
* **虚假被拒** —— 换语句、换见证、改一个分量都必须被拒。

再加上 Fiat-Shamir 的确定性：同一份语句在同一转录下必然得到同一个挑战，
所以两次独立生成应当得到逐位相同的证明（可复现性），
而语句一变挑战就变（绑定性）。
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from svc import DeterministicRNG
from svc.pok import (
    PoKComSubProof,
    PoKOpenProof,
    PoKSubVProof,
    PoProd2CRS,
    PoProd2Proof,
    Transcript,
    describe,
    hash_to_prime,
    pokcomsub_prove,
    pokcomsub_verify,
    pokopen_prove,
    pokopen_verify,
    poksubv_prove,
    poksubv_verify,
    poprod2_prove,
    poprod2_verify,
    poprodstar_prove,
    poprodstar_verify,
)
from svc.yinyan import (
    commit1,
    disagg1,
    open1,
    partnd_prime_prod,
    prime_prod,
    setup1,
    specialize1,
)

MODULUS_BITS = 256
LAMBDA = 16

#: ``PoKSubV`` 的转录标签（与实现里 :func:`~svc.pok.poksubv_prove` 的域分隔字符串一致）
POKSUBV_LABEL = "poksubv"


@pytest.fixture(scope="module")
def crs():
    return setup1(
        lambda_bits=LAMBDA, k=1, n=16, rng=DeterministicRNG(b"pytest-pok"),
        modulus_bits=MODULUS_BITS,
    )


@pytest.fixture(scope="module")
def crsn(crs):
    return specialize1(crs, 16)


@pytest.fixture(scope="module")
def committed(crsn):
    rng = DeterministicRNG(b"pytest-pok-vals")
    vals = tuple(rng.randbelow(2) for _ in range(crsn.n))
    C, aux = commit1(crsn, vals)
    return crsn, C, vals, aux


@pytest.fixture(scope="module")
def pp2(crs) -> PoProd2CRS:
    return PoProd2CRS(
        N=crs.N, g1=crs.g0, g2=crs.g1, g3=crs.g, lambda_bits=LAMBDA
    )


@pytest.fixture(scope="module")
def ab():
    r"""一对 200 位以上的指数。

    指数必须比挑战素数 :math:`\ell`（:math:`2\lambda = 32` 位）大得多，
    否则 ``q_a = q_b = q_c = 0``，证明退化成 ``(QY, QC) = (1, 1)``，
    验证等式与 :math:`\ell` 无关 —— 那样的用例测不到挑战绑定。
    """
    rng = DeterministicRNG(b"pytest-poprod-ab")
    return rng.randbelow(1 << 200), rng.randbelow(1 << 200)


# ---------------------------------------------------------------------------
# 转录与哈希到素数
# ---------------------------------------------------------------------------

class TestTranscript:
    def test_同一转录同一挑战(self):
        a = Transcript("t", 1, 2, 3).challenge_prime(32)
        b = Transcript("t", 1, 2, 3).challenge_prime(32)
        assert a == b

    def test_语句不同挑战就不同(self):
        a = Transcript("t", 1, 2, 3).challenge_prime(32)
        b = Transcript("t", 1, 2, 4).challenge_prime(32)
        assert a != b

    def test_标签不同挑战就不同(self):
        assert (Transcript("t1", 1).challenge_prime(32)
                != Transcript("t2", 1).challenge_prime(32))

    def test_连续取多个挑战互不相同(self):
        t = Transcript("t", 1)
        got = [t.challenge_int(64) for _ in range(5)]
        assert len(set(got)) == 5

    def test_吸附之后计数重置(self):
        t = Transcript("t", 1)
        first = t.challenge_int(64)
        t.absorb(2)
        assert t.challenge_int(64) != first

    def test_challenge_group_落在群内(self, crs):
        h = Transcript("t", 1).challenge_group(crs.g, crs.N)
        assert 0 < h < crs.N


class TestHashToPrime:
    @pytest.mark.parametrize("bits", [8, 16, 32, 64])
    def test_输出是素数且位长正确(self, bits):
        from svc.mathbase import is_probable_prime

        p = hash_to_prime(b"hello", bits)
        assert is_probable_prime(p)
        assert p.bit_length() >= bits - 1
        assert p == hash_to_prime(b"hello", bits)   # 确定性

    def test_输入不同输出不同(self):
        assert hash_to_prime(b"a", 32) != hash_to_prime(b"b", 32)

    def test_位长过小报错(self):
        with pytest.raises(ValueError):
            hash_to_prime(b"x", 2)


# ---------------------------------------------------------------------------
# PoProd2
# ---------------------------------------------------------------------------

class TestPoProd2:
    def test_诚实通过(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        proof = poprod2_prove(pp2, Y, C, a, b, Transcript("pp2", crs.N))
        assert proof.QY != 1 and proof.QC != 1
        assert poprod2_verify(pp2, Y, C, proof, Transcript("pp2", crs.N))

    def test_替换语句被拒(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        proof = poprod2_prove(pp2, Y, C, a, b, Transcript("pp2", crs.N))
        assert not poprod2_verify(pp2, Y * 2 % crs.N, C, proof,
                                 Transcript("pp2", crs.N))
        assert not poprod2_verify(pp2, Y, C * 2 % crs.N, proof,
                                 Transcript("pp2", crs.N))

    def test_换转录被拒(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        proof = poprod2_prove(pp2, Y, C, a, b, Transcript("pp2", crs.N))
        assert not poprod2_verify(pp2, Y, C, proof, Transcript("other", crs.N))

    def test_换域分隔常量被拒(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        proof = poprod2_prove(pp2, Y, C, a, b, Transcript("pp2", crs.N, b"ctx"))
        assert not poprod2_verify(pp2, Y, C, proof, Transcript("pp2", crs.N))

    def test_余数越界被拒(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        proof = poprod2_prove(pp2, Y, C, a, b, Transcript("pp2", crs.N))
        bad = PoProd2Proof(proof.QY, proof.QC, proof.ra + (1 << 200), proof.rb)
        assert not poprod2_verify(pp2, Y, C, bad, Transcript("pp2", crs.N))

    def test_交换两个余数被拒(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        proof = poprod2_prove(pp2, Y, C, a, b, Transcript("pp2", crs.N))
        bad = PoProd2Proof(proof.QY, proof.QC, proof.rb, proof.ra)
        assert not poprod2_verify(pp2, Y, C, bad, Transcript("pp2", crs.N))

    def test_指数不对时证明不成立(self, crs, pp2, ab):
        # 用 (a, b) 去证明 (a, b+1) 的语句：诚实算出的证明必然不通过
        a, b = ab
        Y_wrong = pow(crs.g0, a, crs.N) * pow(crs.g1, b + 1, crs.N) % crs.N
        C_wrong = pow(crs.g, a * (b + 1), crs.N)
        proof = poprod2_prove(pp2, Y_wrong, C_wrong, a, b,
                              Transcript("pp2", crs.N))
        assert not poprod2_verify(pp2, Y_wrong, C_wrong, proof,
                                  Transcript("pp2", crs.N))


# ---------------------------------------------------------------------------
# PoProd*
# ---------------------------------------------------------------------------

class TestPoProdStar:
    def test_诚实通过(self, crs, ab):
        rng = DeterministicRNG(b"poprodstar")
        a, b = ab
        Gamma = pow(crs.g, rng.randbelow(1 << 40), crs.N)
        Delta = pow(crs.g, rng.randbelow(1 << 40), crs.N)
        A = pow(Gamma, a, crs.N)
        B = pow(Delta, b, crs.N)
        C = pow(crs.g, a * b, crs.N)
        proof = poprodstar_prove(crs.N, crs.g, A, B, C, Gamma, Delta, a, b,
                                 Transcript("pps", crs.N), LAMBDA)
        assert poprodstar_verify(crs.N, crs.g, A, B, C, Gamma, Delta, proof,
                                 Transcript("pps", crs.N), LAMBDA)

    @pytest.mark.parametrize("which", ["A", "B", "C", "Gamma", "Delta"])
    def test_替换任一分量被拒(self, crs, ab, which):
        rng = DeterministicRNG(b"poprodstar-bad")
        a, b = ab
        Gamma = pow(crs.g, rng.randbelow(1 << 40), crs.N)
        Delta = pow(crs.g, rng.randbelow(1 << 40), crs.N)
        A, B = pow(Gamma, a, crs.N), pow(Delta, b, crs.N)
        C = pow(crs.g, a * b, crs.N)
        proof = poprodstar_prove(crs.N, crs.g, A, B, C, Gamma, Delta, a, b,
                                 Transcript("pps", crs.N), LAMBDA)
        st = {
            "A": (A * 2 % crs.N, B, C, Gamma, Delta),
            "B": (A, B * 2 % crs.N, C, Gamma, Delta),
            "C": (A, B, C * 2 % crs.N, Gamma, Delta),
            "Gamma": (A, B, C, Gamma * 2 % crs.N, Delta),
            "Delta": (A, B, C, Gamma, Delta * 2 % crs.N),
        }[which]
        assert not poprodstar_verify(crs.N, crs.g, *st, proof,
                                     Transcript("pps", crs.N), LAMBDA)

    def test_换转录被拒(self, crs, ab):
        rng = DeterministicRNG(b"poprodstar-t")
        a, b = ab
        Gamma = pow(crs.g, rng.randbelow(1 << 40), crs.N)
        Delta = pow(crs.g, rng.randbelow(1 << 40), crs.N)
        A, B = pow(Gamma, a, crs.N), pow(Delta, b, crs.N)
        C = pow(crs.g, a * b, crs.N)
        proof = poprodstar_prove(crs.N, crs.g, A, B, C, Gamma, Delta, a, b,
                                 Transcript("pps", crs.N), LAMBDA)
        assert not poprodstar_verify(crs.N, crs.g, A, B, C, Gamma, Delta, proof,
                                     Transcript("other", crs.N), LAMBDA)


# ---------------------------------------------------------------------------
# PoKOpen
# ---------------------------------------------------------------------------

class TestPoKOpen:
    def test_诚实通过(self, crs, crsn, committed):
        crsn, C, vals, aux = committed
        I = [0, 1, 2]
        pi = open1(crs, I, [vals[i] for i in I], aux)
        a_I, b_I = partnd_prime_prod(crs.primegen, I, [vals[i] for i in I], 1)[0]
        u_I = prime_prod(crs.primegen, I)
        proof = pokopen_prove(crs.N, crs.g, C.A[0], C.B[0],
                              pi.Gamma[0], pi.Delta[0], a_I, b_I, u_I,
                              Transcript("pokopen", crs.N), LAMBDA)
        assert pokopen_verify(crs.N, crs.g, C.A[0], C.B[0], u_I, proof,
                              Transcript("pokopen", crs.N), LAMBDA)

    def test_锚点被换就失败(self, crs, crsn, committed):
        crsn, C, vals, aux = committed
        I = [0, 1, 2]
        pi = open1(crs, I, [vals[i] for i in I], aux)
        a_I, b_I = partnd_prime_prod(crs.primegen, I, [vals[i] for i in I], 1)[0]
        u_I = prime_prod(crs.primegen, I)
        proof = pokopen_prove(crs.N, crs.g, C.A[0], C.B[0],
                              pi.Gamma[0], pi.Delta[0], a_I, b_I, u_I,
                              Transcript("pokopen", crs.N), LAMBDA)
        # 验证方自己算 U_I，换一个下标集合就锚不上了
        assert not pokopen_verify(crs.N, crs.g, C.A[0], C.B[0],
                                  prime_prod(crs.primegen, [0, 1]), proof,
                                  Transcript("pokopen", crs.N), LAMBDA)

    def test_语句被换就失败(self, crs, crsn, committed):
        crsn, C, vals, aux = committed
        I = [0, 1, 2]
        pi = open1(crs, I, [vals[i] for i in I], aux)
        a_I, b_I = partnd_prime_prod(crs.primegen, I, [vals[i] for i in I], 1)[0]
        u_I = prime_prod(crs.primegen, I)
        proof = pokopen_prove(crs.N, crs.g, C.A[0], C.B[0],
                              pi.Gamma[0], pi.Delta[0], a_I, b_I, u_I,
                              Transcript("pokopen", crs.N), LAMBDA)
        assert not pokopen_verify(crs.N, crs.g, C.A[0] * 3 % crs.N, C.B[0],
                                  u_I, proof, Transcript("pokopen", crs.N),
                                  LAMBDA)

    def test_证明里塞进别的_Gamma_就失败(self, crs, crsn, committed):
        crsn, C, vals, aux = committed
        I = [0, 1, 2]
        pi = open1(crs, I, [vals[i] for i in I], aux)
        a_I, b_I = partnd_prime_prod(crs.primegen, I, [vals[i] for i in I], 1)[0]
        u_I = prime_prod(crs.primegen, I)
        proof = pokopen_prove(crs.N, crs.g, C.A[0], C.B[0],
                              pi.Gamma[0], pi.Delta[0], a_I, b_I, u_I,
                              Transcript("pokopen", crs.N), LAMBDA)
        bad = PoKOpenProof(proof.Gamma_I * 2 % crs.N, proof.Delta_I, proof.prod)
        assert not pokopen_verify(crs.N, crs.g, C.A[0], C.B[0], u_I, bad,
                                  Transcript("pokopen", crs.N), LAMBDA)


# ---------------------------------------------------------------------------
# PoKSubV
# ---------------------------------------------------------------------------

def _subv_statement(crs, crsn, vals, aux, m):
    """构造 ``C'`` 承诺 ``C`` 在 ``[0, m)`` 上子向量的一组见证。"""
    I = list(range(m))
    vals_I = [vals[i] for i in I]
    pi_all = open1(crs, list(range(crsn.n)), vals, aux)
    pi_sub = disagg1(crs, list(range(crsn.n)), vals, pi_all, I)
    crsn_p = specialize1(crs, m)
    C_p, _ = commit1(crsn_p, vals_I, with_prod=False)
    a_I, b_I = partnd_prime_prod(crs.primegen, I, vals_I, 1)[0]
    return I, vals_I, pi_sub, C_p, crsn_p, a_I, b_I


class TestPoKSubV:
    def test_诚实通过(self, crs, crsn, committed):
        _, C, vals, aux = committed
        m = 4
        I, vals_I, pi_sub, C_p, crsn_p, a_I, b_I = _subv_statement(
            crs, crsn, vals, aux, m
        )
        proof = poksubv_prove(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, crsn_p.U_n, pi_sub.Gamma[0], pi_sub.Delta[0], a_I, b_I,
            Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )
        assert poksubv_verify(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, crsn_p.U_n, proof, Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )

    def test_换_C_撇的第二个累加器就失败(self, crs, crsn, committed):
        _, C, vals, aux = committed
        m = 4
        I, vals_I, pi_sub, C_p, crsn_p, a_I, b_I = _subv_statement(
            crs, crsn, vals, aux, m
        )
        proof = poksubv_prove(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, crsn_p.U_n, pi_sub.Gamma[0], pi_sub.Delta[0], a_I, b_I,
            Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )
        assert not poksubv_verify(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0],
            C_p.A[0], C_p.B[0] * 2 % crs.N,
            crsn.U_n, crsn_p.U_n, proof, Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )

    def test_换新长度锚点就失败(self, crs, crsn, committed):
        _, C, vals, aux = committed
        m = 4
        I, vals_I, pi_sub, C_p, crsn_p, a_I, b_I = _subv_statement(
            crs, crsn, vals, aux, m
        )
        proof = poksubv_prove(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, crsn_p.U_n, pi_sub.Gamma[0], pi_sub.Delta[0], a_I, b_I,
            Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )
        other_U = specialize1(crs, m + 1).U_n
        assert not poksubv_verify(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, other_U, proof, Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )

    def test_用另一组指数生成的证明不通用(self, crs, crsn, committed):
        """拿子向量 `[0, 4)` 的证明去冒充 `[0, 6)` 的子向量。"""
        _, C, vals, aux = committed
        m = 4
        I, vals_I, pi_sub, C_p, crsn_p, a_I, b_I = _subv_statement(
            crs, crsn, vals, aux, m
        )
        proof = poksubv_prove(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, crsn_p.U_n, pi_sub.Gamma[0], pi_sub.Delta[0], a_I, b_I,
            Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )
        C_big, _ = commit1(specialize1(crs, 6), vals[:6], with_prod=False)
        assert not poksubv_verify(
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0],
            C_big.A[0], C_big.B[0], crsn.U_n, specialize1(crs, 6).U_n,
            proof, Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )

    def test_可复现(self, crs, crsn, committed):
        _, C, vals, aux = committed
        m = 4
        I, vals_I, pi_sub, C_p, crsn_p, a_I, b_I = _subv_statement(
            crs, crsn, vals, aux, m
        )
        mk = lambda: poksubv_prove(  # noqa: E731
            crs.N, crs.g, crs.g0, crs.g1, C.A[0], C.B[0], C_p.A[0], C_p.B[0],
            crsn.U_n, crsn_p.U_n, pi_sub.Gamma[0], pi_sub.Delta[0], a_I, b_I,
            Transcript(POKSUBV_LABEL, crs.N), LAMBDA,
        )
        assert mk() == mk()


# ---------------------------------------------------------------------------
# PoKComSub（§6.3）
# ---------------------------------------------------------------------------

def _comsub_stmt(crs, n1, n2, size, seed):
    """造两个承诺，它们在 ``I = [0, size)`` 上共享同一段子向量。

    共享段取交替的 0/1，保证 :math:`a_I, b_I` 都不退化为 1，
    否则证明里的 ``q_a`` 会是 0、多个分量恒等于 1，测不出绑定关系。
    """
    rng = DeterministicRNG(seed)
    I = list(range(size))
    shared = [i % 2 for i in range(size)]
    v1 = shared + [rng.randbelow(2) for _ in range(n1 - size)]
    v2 = shared + [rng.randbelow(2) for _ in range(n2 - size)]
    crsn1, crsn2 = specialize1(crs, n1), specialize1(crs, n2)
    C1, _ = commit1(crsn1, v1, with_prod=False)
    C2, _ = commit1(crsn2, v2, with_prod=False)
    pi1 = open1(crs, I, shared, v1)
    pi2 = open1(crs, I, shared, v2)
    a_I, b_I = partnd_prime_prod(crs.primegen, I, shared, 1)[0]
    u_I = prime_prod(crs.primegen, I)
    return C1, C2, pi1, pi2, a_I, b_I, u_I, shared


class TestPoKComSub:
    @pytest.fixture(scope="class")
    def stmt(self, crs):
        return _comsub_stmt(crs, 12, 9, 6, b"pytest-comsub")

    def test_诚实通过(self, crs, stmt):
        C1, C2, pi1, pi2, a_I, b_I, u_I, _ = stmt
        proof = pokcomsub_prove(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0],
            pi1.Gamma[0], pi1.Delta[0], pi2.Gamma[0], pi2.Delta[0],
            a_I, b_I, u_I, Transcript("comsub", crs.N), LAMBDA,
        )
        assert pokcomsub_verify(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0], u_I, proof,
            Transcript("comsub", crs.N), LAMBDA,
        )

    def test_第二个承诺被换就失败(self, crs, stmt):
        C1, C2, pi1, pi2, a_I, b_I, u_I, _ = stmt
        proof = pokcomsub_prove(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0],
            pi1.Gamma[0], pi1.Delta[0], pi2.Gamma[0], pi2.Delta[0],
            a_I, b_I, u_I, Transcript("comsub", crs.N), LAMBDA,
        )
        assert not pokcomsub_verify(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0] * 3 % crs.N, C2.B[0],
            u_I, proof, Transcript("comsub", crs.N), LAMBDA,
        )

    def test_锚点下标集合被换就失败(self, crs, stmt):
        C1, C2, pi1, pi2, a_I, b_I, u_I, _ = stmt
        proof = pokcomsub_prove(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0],
            pi1.Gamma[0], pi1.Delta[0], pi2.Gamma[0], pi2.Delta[0],
            a_I, b_I, u_I, Transcript("comsub", crs.N), LAMBDA,
        )
        other_u = prime_prod(crs.primegen, [0, 1, 2, 3])
        assert not pokcomsub_verify(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0], other_u, proof,
            Transcript("comsub", crs.N), LAMBDA,
        )

    def test_换一个不共享的向量就失败(self, crs, stmt):
        """构造一个在 ``I`` 上取值不同的向量，它的承诺不能被拿来冒充。"""
        C1, C2, pi1, pi2, a_I, b_I, u_I, shared = stmt
        proof = pokcomsub_prove(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0],
            pi1.Gamma[0], pi1.Delta[0], pi2.Gamma[0], pi2.Delta[0],
            a_I, b_I, u_I, Transcript("comsub", crs.N), LAMBDA,
        )
        rng = DeterministicRNG(b"pytest-comsub-other")
        bad = [1 - v for v in shared] + [rng.randbelow(2) for _ in range(3)]
        C_bad, _ = commit1(specialize1(crs, 9), bad, with_prod=False)
        assert not pokcomsub_verify(
            crs.N, crs.g, C1.A[0], C1.B[0], C_bad.A[0], C_bad.B[0], u_I,
            proof, Transcript("comsub", crs.N), LAMBDA,
        )

    def test_两次打开被迫共用同一个盲化底数(self, crs, stmt):
        """两条底数等式共用 :math:`z_a = h^{a_I}`，换掉就两边一起崩。"""
        C1, C2, pi1, pi2, a_I, b_I, u_I, _ = stmt
        proof = pokcomsub_prove(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0],
            pi1.Gamma[0], pi1.Delta[0], pi2.Gamma[0], pi2.Delta[0],
            a_I, b_I, u_I, Transcript("comsub", crs.N), LAMBDA,
        )
        assert proof.QA1 != 1 and proof.QB1 != 1     # 共享段非退化
        bad = replace(proof, za=proof.za * 2 % crs.N)
        assert not pokcomsub_verify(
            crs.N, crs.g, C1.A[0], C1.B[0], C2.A[0], C2.B[0], u_I, bad,
            Transcript("comsub", crs.N), LAMBDA,
        )


# ---------------------------------------------------------------------------
# 杂项
# ---------------------------------------------------------------------------

class TestDescribe:
    def test_每个证明类型都有可读描述(self, crs, pp2, ab):
        a, b = ab
        Y = pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        C = pow(crs.g, a * b, crs.N)
        p2 = poprod2_prove(pp2, Y, C, a, b, Transcript("x", crs.N))
        ps = poprodstar_prove(crs.N, crs.g, Y, C, C, crs.g0, crs.g1, a, b,
                              Transcript("y", crs.N), LAMBDA)
        ko = PoKOpenProof(1, 2, ps)
        kv = PoKSubVProof(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
        kc = PoKComSubProof(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13)
        for obj in (p2, ps, ko, kv, kc):
            assert describe(obj)
