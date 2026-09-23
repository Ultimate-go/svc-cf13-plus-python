"""素数映射测试 —— 清单 #9 / #10 / #11。

这一层的**唯一**硬要求是「互不相同」。原因不是洁癖：
:func:`~svc.mathbase.shamir_trick` 在 ``gcd(e_i, e_j) != 1`` 时会
**静默返回错误结果**（不崩溃、不报错，只是算错），
所以「映射是单射」这条性质必须被测试钉死。
"""

from __future__ import annotations

import math

import pytest

from svc import DeterministicRNG, generate_primes
from svc.mathbase import (
    is_bpsw_prime,
    is_probable_prime,
    is_strong_lucas_prp,
    jacobi_symbol,
)
from svc.primegen import PrimeGen, PrimeGenHash

L = 16          # 元素位长
BITS = L + 1    # 素数位长


class TestGeneratePrimes:
    def test_模数位长精确(self):
        for bits in (64, 128, 256):
            N, g = generate_primes(DeterministicRNG(b"t"), bits)
            assert N.bit_length() == bits, "N 的位长必须恰好等于请求的 bits"

    def test_生成元是单位元(self):
        """``g`` 必须是 :math:`\\mathbb{Z}_N^{*}` 里的单位，且落在 ``[2, N)``。"""
        N, g = generate_primes(DeterministicRNG(b"t"), 256)
        assert 2 <= g < N
        assert math.gcd(g, N) == 1, "生成元必须与 N 互素，否则根本不是群元素"

    def test_生成元是随机抽取的(self):
        """论文写 :math:`g \\leftarrow\\$ \\mathbb{G}` —— 不同种子必须给出不同 ``g``。

        这条以前是反过来的（断言 ``g == 65547 % N``）：固定生成元让任何人
        都能预知公开参数。改成随机抽取后，断言也要跟着反过来。
        """
        gs = {
            generate_primes(DeterministicRNG(f"gs-{i}".encode()), 256)[1]
            for i in range(6)
        }
        assert len(gs) == 6, f"6 个种子应给出 6 个不同的 g，实得 {len(gs)} 个"

    def test_生成元不落回旧常量(self):
        N, g = generate_primes(DeterministicRNG(b"t"), 256)
        assert g != 65547 % N, "g 不该再是那个写死的 RSA_DEFAULT_EXPONENT"

    def test_N_是合数且无小因子(self):
        N, _ = generate_primes(DeterministicRNG(b"t"), 256)
        assert not is_probable_prime(N)
        for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
            assert N % p != 0

    def test_可复现(self):
        a = generate_primes(DeterministicRNG(b"same"), 256)
        b = generate_primes(DeterministicRNG(b"same"), 256)
        assert a == b, "(N, g) 两者都必须可复现"

    def test_不同种子得到不同群(self):
        a = generate_primes(DeterministicRNG(b"s1"), 256)
        b = generate_primes(DeterministicRNG(b"s2"), 256)
        assert a[0] != b[0]

    def test_位长太小报错(self):
        with pytest.raises(ValueError):
            generate_primes(DeterministicRNG(b"t"), 32)


class TestPrimeGen:
    def test_全部素数都是指定位长(self):
        pg = PrimeGen(max_sz=64, bits=BITS)
        primes = pg.first(64)
        assert len(primes) == 64
        for p in primes:
            assert is_probable_prime(p)
            assert p.bit_length() == BITS

    def test_严格递增且互不相同(self):
        """双射的核心保证：顺序扫描必然互不相同。"""
        pg = PrimeGen(max_sz=128, bits=BITS)
        primes = pg.first(128)
        assert primes == sorted(primes)
        assert len(set(primes)) == 128

    def test_起点是最小的指定位长数(self):
        pg = PrimeGen(max_sz=1, bits=BITS)
        assert pg.get(0) >= 1 << (BITS - 1)

    def test_惰性求值(self):
        pg = PrimeGen(max_sz=1000000, bits=BITS)
        assert pg.computed == 0
        pg.get(3)
        assert 0 < pg.computed < 1000, "不该为了取第 4 个素数就把一百万个全算出来"

    def test_get_与_get_many_一致(self):
        pg = PrimeGen(max_sz=32, bits=BITS)
        assert pg.get_many([0, 5, 9, 31]) == [pg.get(0), pg.get(5), pg.get(9), pg.get(31)]

    def test_下标越界(self):
        pg = PrimeGen(max_sz=8, bits=BITS)
        with pytest.raises(IndexError):
            pg.get(8)
        with pytest.raises(IndexError):
            pg.get(-1)

    def test_位长不足时明确报错(self):
        """l 太小时该位长的素数不够用，必须报错而不是悄悄用超范围素数。"""
        # 5 位素数只有 17,19,23,29,31 共 5 个
        pg = PrimeGen(max_sz=8, bits=5)
        with pytest.raises(ValueError, match="位素数已经用尽"):
            pg.first(8)

    def test_边界内可以取满(self):
        pg = PrimeGen(max_sz=5, bits=5)
        assert pg.first(5) == [17, 19, 23, 29, 31]


class TestPrimeGenHash:
    def test_正常位数下互不相同(self):
        pg = PrimeGenHash(max_sz=64, prime_bytes=16)
        primes = pg.first(64)
        assert len(set(primes)) == 64
        for p in primes:
            assert is_probable_prime(p)

    def test_位数太小时碰撞被抓住(self):
        """素数不足时哈希版必然碰撞 —— 必须抛异常，不能带着错继续算。"""
        pg = PrimeGenHash(max_sz=64, prime_bytes=1, check_distinct=True)
        with pytest.raises(ValueError, match="碰撞"):
            pg.first(64)

    def test_可关闭检查以观察碰撞(self):
        pg = PrimeGenHash(max_sz=64, prime_bytes=1, check_distinct=False)
        primes = pg.first(64)
        assert len(set(primes)) < 64

# ---------------------------------------------------------------------------
# 【6】素性判据：超出「确定性基」覆盖范围之后用 BPSW
# ---------------------------------------------------------------------------

def _sieve(limit: int) -> list[bool]:
    flags = [True] * limit
    flags[0] = flags[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if flags[i]:
            for j in range(i * i, limit, i):
                flags[j] = False
    return flags


def _spsp_to_base2(n: int) -> bool:
    """n 是不是 base-2 强可能素数（独立实现，只用来构造测试样本）。"""
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(2, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


#: 已知的 base-2 强伪素数：base-2 判据放行，**必须**由 Lucas 判据拦下。
BASE2_STRONG_PSEUDOPRIMES = (
    2047, 3277, 4033, 4681, 8321, 15841, 29341, 42799, 49141, 52633,
    65281, 74665, 80581, 85489, 88357, 90751, 104653, 130561, 196093,
    220729, 233017, 252601, 253241, 256999, 271951, 280601, 314821,
    357761, 390937, 458989, 476971, 486737,
)

#: 更大的两个「多基强伪素数」：前几个素数为基的 MR 也会被它们骗过。
MULTI_BASE_STRONG_PSEUDOPRIMES = (3215031751, 3825123056546413051)

#: 超出固定基覆盖范围的已知素数（3.3e24 < 2^127 - 1）。
BIG_PRIMES = ((1 << 127) - 1, (1 << 89) - 1, (1 << 521) - 1)


class TestBPSW:
    def test_与试除法逐一对齐(self):
        limit = 20000
        flags = _sieve(limit)
        wrong = [n for n in range(limit) if is_bpsw_prime(n) != flags[n]]
        assert wrong == []

    def test_is_probable_prime_在小范围也不出错(self):
        limit = 20000
        flags = _sieve(limit)
        wrong = [n for n in range(limit) if is_probable_prime(n) != flags[n]]
        assert wrong == []

    def test_base2_强伪素数被拦下(self):
        """这一组是【6】的核心：只有 base-2 判据时它们会漏过去。"""
        for n in BASE2_STRONG_PSEUDOPRIMES:
            assert _spsp_to_base2(n), f"{n} 本应通过 base-2 判据"
            assert not is_bpsw_prime(n), f"BPSW 漏掉了 {n}"
            assert not is_probable_prime(n), f"is_probable_prime 漏掉了 {n}"

    def test_多基强伪素数被拦下(self):
        for n in MULTI_BASE_STRONG_PSEUDOPRIMES:
            assert not is_probable_prime(n)

    def test_超出确定基范围的大素数通过(self):
        for p in BIG_PRIMES:
            assert p > 3_317_044_064_679_887_385_961_981
            assert is_bpsw_prime(p)
            assert is_probable_prime(p)

    def test_超出确定基范围的大合数被拒(self):
        a, b = BIG_PRIMES[0], BIG_PRIMES[1]
        n = a * b
        assert not is_probable_prime(n)
        # 完全平方数也要挡住（Lucas 参数搜索对平方数会死循环）
        assert not is_probable_prime(a * a)

    def test_判据是确定性的(self):
        """同一个 n 必须给出同一个结论 —— 这是不能改用真随机基的理由。"""
        n = BIG_PRIMES[0]
        assert len({is_probable_prime(n) for _ in range(5)}) == 1
        assert len({is_bpsw_prime(n) for _ in range(5)}) == 1

    def test_显式的额外轮数不改变结论(self):
        for p in BIG_PRIMES:
            assert is_probable_prime(p, rounds=0)
            assert is_probable_prime(p, rounds=40)
        n = BIG_PRIMES[0] * BIG_PRIMES[1]
        assert not is_probable_prime(n, rounds=40)

    def test_可以关掉_bpsw(self):
        """``bpsw=False`` 时退回「只跑确定基 + 显式轮数」的老路。"""
        assert is_probable_prime(BIG_PRIMES[0], bpsw=False, rounds=40)
        assert is_probable_prime(BIG_PRIMES[0], bpsw=False, rounds=0)

    def test_单独的强_Lucas_判据(self):
        assert is_strong_lucas_prp(2)
        assert is_strong_lucas_prp(97)
        for n in BASE2_STRONG_PSEUDOPRIMES:
            assert not is_strong_lucas_prp(n)

    def test_Jacobi_符号与欧拉判据一致(self):
        """对**素数** n，Jacobi 符号必须等于欧拉判据的结果。"""
        flags = _sieve(400)
        for n in range(3, 400, 2):
            if not flags[n]:
                continue
            for a in range(n):
                ref = pow(a, (n - 1) // 2, n)
                ref = -1 if ref == n - 1 else ref
                assert jacobi_symbol(a, n) == ref, (a, n)

    def test_Jacobi_符号要求正奇数(self):
        with pytest.raises(ValueError, match="正奇数"):
            jacobi_symbol(3, 8)
        with pytest.raises(ValueError, match="正奇数"):
            jacobi_symbol(3, 0)

