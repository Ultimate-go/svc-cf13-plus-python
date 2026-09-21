"""论文 §5.1 阴阳方案的测试。

覆盖四条性质：

1. **不变量** —— ``PartndPrimeProd`` 的每个比特位上都有 :math:`a_j \\cdot b_j = u_I`，
   这是整套方案（包括 §8.1 的 VDS1）成立的地基；
2. **打开与验证** —— 任意子集都能打开、能验证；
3. **增量** —— ``Disagg`` 拆出的两份能各自验证，``Agg`` 合回去仍然验证通过；
4. **攻击面** —— 改值、篡改 Γ、抽掉 PoProd2 都必须被拒。
"""

from __future__ import annotations

import pytest

from svc import DeterministicRNG
from svc.pok import PoProd2Proof
from svc.yinyan import (
    CRS1,
    CRSn1,
    Commitment1,
    Opening1,
    agg1,
    agg_many_to_one1,
    commit1,
    complement,
    disagg1,
    open1,
    partnd_prime_prod,
    prime_prod,
    setup1,
    specialize1,
    ver1,
)

MODULUS_BITS = 256
LAMBDA = 16


# ---------------------------------------------------------------------------
# 夹具
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def crs() -> CRS1:
    return setup1(
        lambda_bits=LAMBDA, k=1, n=32, rng=DeterministicRNG(b"pytest-yinyan"),
        modulus_bits=MODULUS_BITS,
    )


@pytest.fixture(scope="module")
def crsn(crs) -> CRSn1:
    return specialize1(crs, 16)


@pytest.fixture(scope="module")
def committed(crsn):
    rng = DeterministicRNG(b"pytest-yinyan-vals")
    vals = tuple(rng.randbelow(2) for _ in range(crsn.n))
    C, aux = commit1(crsn, vals)
    return crsn, C, vals, aux


@pytest.fixture(scope="module")
def crs2() -> CRS1:
    """块宽 ``k = 2`` 的 CRS。"""
    return setup1(
        lambda_bits=LAMBDA, k=2, n=16, rng=DeterministicRNG(b"pytest-yinyan-k2"),
        modulus_bits=MODULUS_BITS,
    )


# ---------------------------------------------------------------------------
# 不变量与辅助函数
# ---------------------------------------------------------------------------

class TestPrimeProducts:
    def test_prime_prod_是连乘(self, crs):
        assert prime_prod(crs.primegen, [0, 1, 2]) == (
            crs.primegen.get(0) * crs.primegen.get(1) * crs.primegen.get(2)
        )
        assert prime_prod(crs.primegen, []) == 1

    def test_partnd_两个分量之积等于全体(self, crs):
        I = [0, 1, 2, 3, 4, 5]
        vals = [0, 1, 1, 0, 1, 0]
        (a, b), = partnd_prime_prod(crs.primegen, I, vals, 1)
        assert a * b == prime_prod(crs.primegen, I)

    def test_partnd_k_个比特位上各自成立(self, crs2):
        I = list(range(8))
        vals = [0b11, 0b00, 0b10, 0b01, 0b11, 0b10, 0b00, 0b01]
        pairs = partnd_prime_prod(crs2.primegen, I, vals, 2)
        u_I = prime_prod(crs2.primegen, I)
        assert len(pairs) == 2
        for a, b in pairs:
            assert a * b == u_I

    def test_partnd_下标的取值与素数一一对应(self, crs):
        # 单元素集合：值为 0 时 (p_i, 1)，值为 1 时 (1, p_i)
        p = crs.primegen.get(7)
        assert partnd_prime_prod(crs.primegen, [7], [0], 1) == [(p, 1)]
        assert partnd_prime_prod(crs.primegen, [7], [1], 1) == [(1, p)]

    def test_partnd_长度不匹配报错(self, crs):
        with pytest.raises(ValueError):
            partnd_prime_prod(crs.primegen, [0, 1], [0], 1)

    def test_complement(self):
        assert complement([1, 3], 5) == [0, 2, 4]
        assert complement([], 3) == [0, 1, 2]
        assert complement(list(range(3)), 3) == []


class TestSetup:
    def test_三个生成元互不相同(self, crs):
        assert len({crs.g, crs.g0, crs.g1}) == 3
        assert crs.k == 1
        assert crs.bits == MODULUS_BITS

    def test_specialize_定点累加器(self, crs):
        crsn = specialize1(crs, 4)
        u_4 = prime_prod(crs.primegen, range(4))
        assert crsn.u_n == u_4
        assert crsn.U_n == pow(crs.g, u_4, crs.N)

    def test_相同种子得到相同参数(self):
        a = setup1(16, 1, 4, rng=DeterministicRNG(b"same"), modulus_bits=MODULUS_BITS)
        b = setup1(16, 1, 4, rng=DeterministicRNG(b"same"), modulus_bits=MODULUS_BITS)
        assert (a.N, a.g, a.g0, a.g1) == (b.N, b.g, b.g0, b.g1)

    def test_非法参数报错(self):
        for args in ((0, 1, 4), (16, 0, 4), (16, 1, 0)):
            with pytest.raises(ValueError):
                setup1(*args, modulus_bits=MODULUS_BITS)


# ---------------------------------------------------------------------------
# VC.Com / Open / Ver
# ---------------------------------------------------------------------------

class TestCommitAndOpen:
    def test_承诺的一对累加器与集合划分一致(self, committed, crs):
        crsn, C, vals, _ = committed
        a, b = partnd_prime_prod(crs.primegen, range(crsn.n), vals, 1)[0]
        assert C.A == (pow(crs.g0, a, crs.N),)
        assert C.B == (pow(crs.g1, b, crs.N),)
        assert C.k == 1

    def test_承诺不变量_两个累加器之积的可验证性(self, committed, crs):
        # A·B = g0^a·g1^b，而 a·b = u_[n]，这正是 PoProd2 所证明的
        crsn, C, vals, _ = committed
        a, b = partnd_prime_prod(crs.primegen, range(crsn.n), vals, 1)[0]
        assert a * b == crsn.u_n
        assert C.product(0) % crs.N == (
            pow(crs.g0, a, crs.N) * pow(crs.g1, b, crs.N) % crs.N
        )

    @pytest.mark.parametrize("size", [0, 1, 2, 5, 8, 16])
    def test_任意大小的子集都能打开并验证(self, committed, crs, size):
        crsn, C, vals, aux = committed
        I = list(range(crsn.n))[:size]
        vals_I = [vals[i] for i in I]
        pi = open1(crs, I, vals_I, aux)
        assert ver1(crsn, C, I, vals_I, pi)

    def test_打开证明自带下标(self, committed, crs):
        crsn, C, vals, aux = committed
        I = [2, 4, 6]
        pi = open1(crs, I, [vals[i] for i in I], aux)
        assert pi.I == (2, 4, 6)

    def test_下标集自动排序归一(self, committed, crs):
        crsn, C, vals, aux = committed
        I = [6, 2, 4]
        pi = open1(crs, I, [vals[i] for i in I], aux)
        assert pi.I == (2, 4, 6)
        assert ver1(crsn, C, [2, 4, 6], [vals[i] for i in (2, 4, 6)], pi)

    def test_空向量承诺报错(self, crsn):
        # §5.1 的 VC.Com 会附 PoProd2，而空向量下这条证明没有意义，
        # 所以直接拒绝；空文件对应的摘要由 §8.1 的 VC.Com' 给出（见 test_vds1）
        with pytest.raises(ValueError):
            commit1(crsn, [])

    def test_越界下标报错(self, committed, crs):
        crsn, C, vals, aux = committed
        with pytest.raises(ValueError):
            open1(crs, [crsn.n], [0], aux)

    def test_值超出块宽报错(self, crsn):
        with pytest.raises(ValueError):
            commit1(crsn, [2])          # k = 1，只允许 0/1


class TestVerifyRejects:
    def test_改一个比特被拒(self, committed, crs):
        crsn, C, vals, aux = committed
        bad = list(vals)
        bad[3] ^= 1
        pi = open1(crs, [3], [bad[3]], bad)
        assert not ver1(crsn, C, [3], [bad[3]], pi)

    def test_篡改_Gamma_被拒(self, committed, crs):
        crsn, C, vals, aux = committed
        I = [0, 1]
        vals_I = [vals[i] for i in I]
        pi = open1(crs, I, vals_I, aux)
        tampered = Opening1((pi.Gamma[0] * 3 % crs.N,), pi.Delta, tuple(I))
        assert not ver1(crsn, C, I, vals_I, tampered)

    def test_篡改_Delta_被拒(self, committed, crs):
        crsn, C, vals, aux = committed
        I = [0, 1]
        vals_I = [vals[i] for i in I]
        pi = open1(crs, I, vals_I, aux)
        tampered = Opening1(pi.Gamma, (pi.Delta[0] * 3 % crs.N,), tuple(I))
        assert not ver1(crsn, C, I, vals_I, tampered)

    def test_证明的下标与请求不符被拒(self, committed, crs):
        crsn, C, vals, aux = committed
        pi = open1(crs, [0], [vals[0]], aux)
        assert not ver1(crsn, C, [1], [vals[1]], pi)

    def test_承诺不带_PoProd2_时默认拒绝(self, committed, crs):
        crsn, C, vals, aux = committed
        I = [0]
        vals_I = [vals[0]]
        pi = open1(crs, I, vals_I, aux)
        no_proof = Commitment1(A=C.A, B=C.B, prod=(), n=C.n)
        assert not ver1(crsn, no_proof, I, vals_I, pi, check_prod=True)
        # 关掉 check_prod 就走 §8.1 的 VC.Ver'
        assert ver1(crsn, no_proof, I, vals_I, pi, check_prod=False)

    def test_伪造的_PoProd2_被拒(self, committed, crs):
        crsn, C, vals, aux = committed
        I = [0]
        vals_I = [vals[0]]
        pi = open1(crs, I, vals_I, aux)
        forged = Commitment1(
            A=C.A, B=C.B, prod=(PoProd2Proof(1, 1, 0, 0),), n=C.n
        )
        assert not ver1(crsn, forged, I, vals_I, pi)

    def test_承诺块宽不匹配被拒(self, committed, crs2):
        crsn, C, vals, aux = committed
        crsn2 = specialize1(crs2, crsn.n)
        assert not ver1(crsn2, C, [0], [vals[0]], open1(crsn.crs, [0], [vals[0]], aux))


# ---------------------------------------------------------------------------
# 增量：Disagg / Agg
# ---------------------------------------------------------------------------

class TestDisagg:
    def test_拆出的两份各自可验证(self, committed, crs):
        crsn, C, vals, aux = committed
        n = crsn.n
        pi_all = open1(crs, list(range(n)), vals, aux)
        lo = disagg1(crs, list(range(n)), vals, pi_all, list(range(n // 2)))
        hi = disagg1(crs, list(range(n)), vals, pi_all, list(range(n // 2, n)))
        assert ver1(crsn, C, list(range(n // 2)), vals[: n // 2], lo)
        assert ver1(crsn, C, list(range(n // 2, n)), vals[n // 2:], hi)

    def test_逐级拆到单元素(self, committed, crs):
        crsn, C, vals, aux = committed
        n = crsn.n
        cur, cur_I = open1(crs, list(range(n)), vals, aux), list(range(n))
        while len(cur_I) > 1:
            half = len(cur_I) // 2
            keep = cur_I[:half]
            cur = disagg1(
                crs, cur_I, [vals[i] for i in cur_I], cur, keep
            )
            cur_I = keep
        assert ver1(crsn, C, cur_I, [vals[i] for i in cur_I], cur)

    def test_非子集报错(self, committed, crs):
        crsn, C, vals, aux = committed
        pi = open1(crs, [0, 1], vals[:2], aux)
        with pytest.raises(ValueError):
            disagg1(crs, [0, 1], vals[:2], pi, [2])


class TestAgg:
    def test_两份合回全体(self, committed, crs):
        crsn, C, vals, aux = committed
        n = crsn.n
        pi_all = open1(crs, list(range(n)), vals, aux)
        lo = disagg1(crs, list(range(n)), vals, pi_all, list(range(n // 2)))
        hi = disagg1(crs, list(range(n)), vals, pi_all, list(range(n // 2, n)))
        merged = agg1(
            crs, list(range(n // 2)), vals[: n // 2], lo,
            list(range(n // 2, n)), vals[n // 2:], hi,
        )
        assert merged.I == tuple(range(n))
        assert ver1(crsn, C, list(range(n)), vals, merged)

    def test_不相交的三份合并(self, committed, crs):
        crsn, C, vals, aux = committed
        n = crsn.n
        pi_all = open1(crs, list(range(n)), vals, aux)
        parts = []
        for start in range(0, n, 4):
            I = list(range(start, min(start + 4, n)))
            parts.append((I, [vals[i] for i in I],
                          disagg1(crs, list(range(n)), vals, pi_all, I)))
        merged = agg_many_to_one1(crs, parts)
        assert ver1(crsn, C, list(range(n)), vals, merged)
        assert merged.I == tuple(range(n))

    def test_合并结果的值顺序按并集排好(self, committed, crs):
        crsn, C, vals, aux = committed
        n = crsn.n
        pi_all = open1(crs, list(range(n)), vals, aux)
        lo = disagg1(crs, list(range(n)), vals, pi_all, list(range(4)))
        hi = disagg1(crs, list(range(n)), vals, pi_all, list(range(4, 8)))
        # 故意反着传，验证实现内部不会把值顺序搞错
        merged = agg1(
            crs, list(range(4, 8)), vals[4:8], hi,
            list(range(4)), vals[:4], lo,
        )
        assert ver1(crsn, C, list(range(8)), vals[:8], merged)

    def test_重叠的两份先拆再合(self, committed, crs):
        crsn, C, vals, aux = committed
        n = crsn.n
        pi_all = open1(crs, list(range(n)), vals, aux)
        left = [0, 1, 2, 3]
        right = [2, 3, 4, 5]
        pi_l = disagg1(crs, list(range(n)), vals, pi_all, left)
        pi_r = disagg1(crs, list(range(n)), vals, pi_all, right)
        merged = agg1(
            crs, left, [vals[i] for i in left], pi_l,
            right, [vals[i] for i in right], pi_r,
        )
        union = [0, 1, 2, 3, 4, 5]
        assert merged.I == tuple(union)
        assert ver1(crsn, C, union, [vals[i] for i in union], merged)

    def test_空列表报错(self, crs):
        with pytest.raises(ValueError):
            agg_many_to_one1(crs, [])


# ---------------------------------------------------------------------------
# 块宽 k > 1
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def k2_block_width(crs2):
    """块宽 ``k = 2`` 的全套测试数据。"""
    crsn = specialize1(crs2, 8)
    rng = DeterministicRNG(b"pytest-yinyan-k2-vals")
    vals = tuple(rng.randbelow(4) for _ in range(8))
    C, aux = commit1(crsn, vals)
    return crsn, C, vals, aux


class TestBlockWidth:
    def test_承诺含_k_对累加器与_k_个_PoProd2(self, k2_block_width):
        crsn, C, _, _ = k2_block_width
        assert C.k == 2
        assert len(C.prod) == 2
        assert len(C.A) == len(C.B) == 2

    @pytest.mark.parametrize("size", [0, 1, 3, 8])
    def test_子集验证(self, crs2, k2_block_width, size):
        crsn, C, vals, aux = k2_block_width
        I = list(range(8))[:size]
        vals_I = [vals[i] for i in I]
        assert ver1(crsn, C, I, vals_I, open1(crs2, I, vals_I, aux))

    def test_拆合(self, crs2, k2_block_width):
        crsn, C, vals, aux = k2_block_width
        pi_all = open1(crs2, list(range(8)), vals, aux)
        lo = disagg1(crs2, list(range(8)), vals, pi_all, list(range(4)))
        hi = disagg1(crs2, list(range(8)), vals, pi_all, list(range(4, 8)))
        assert ver1(crsn, C, list(range(4)), vals[:4], lo)
        assert ver1(crsn, C, list(range(4, 8)), vals[4:], hi)
        merged = agg1(crs2, list(range(4)), vals[:4], lo,
                      list(range(4, 8)), vals[4:], hi)
        assert ver1(crsn, C, list(range(8)), vals, merged)

    def test_去掉一个比特位的_PoProd2_被拒(self, crs2, k2_block_width):
        crsn, C, vals, aux = k2_block_width
        one_short = Commitment1(A=C.A, B=C.B, prod=C.prod[:1], n=C.n)
        assert not ver1(crsn, one_short, [0], [vals[0]],
                        open1(crs2, [0], [vals[0]], aux))

    def test_交换两个比特位的_PoProd2_被拒(self, crs2, k2_block_width):
        crsn, C, vals, aux = k2_block_width
        swapped = Commitment1(A=C.A, B=C.B, prod=(C.prod[1], C.prod[0]), n=C.n)
        assert not ver1(crsn, swapped, [0], [vals[0]],
                        open1(crs2, [0], [vals[0]], aux))
