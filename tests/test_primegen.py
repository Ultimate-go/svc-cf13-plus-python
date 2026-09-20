"""素数映射测试 —— 清单 #9 / #10 / #11。

这一层的**唯一**硬要求是「互不相同」。原因不是洁癖：
:func:`~svc.mathbase.shamir_trick` 在 ``gcd(e_i, e_j) != 1`` 时会
**静默返回错误结果**（不崩溃、不报错，只是算错），
所以「映射是单射」这条性质必须被测试钉死。
"""

from __future__ import annotations

import pytest

from svc import DeterministicRNG, generate_primes
from svc.mathbase import is_probable_prime
from svc.primegen import PrimeGen, PrimeGenHash

L = 16          # 元素位长
BITS = L + 1    # 素数位长


class TestGeneratePrimes:
    def test_模数位长精确(self):
        for bits in (64, 128, 256):
            N, g = generate_primes(DeterministicRNG(b"t"), bits)
            assert N.bit_length() == bits, "N 的位长必须恰好等于请求的 bits"

    def test_生成元取固定值并归约(self):
        N, g = generate_primes(DeterministicRNG(b"t"), 256)
        assert 1 <= g < N
        assert g == 65547 % N

    def test_N_是合数且无小因子(self):
        N, _ = generate_primes(DeterministicRNG(b"t"), 256)
        assert not is_probable_prime(N)
        for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
            assert N % p != 0

    def test_可复现(self):
        a = generate_primes(DeterministicRNG(b"same"), 256)
        b = generate_primes(DeterministicRNG(b"same"), 256)
        assert a == b

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
