"""数学底座测试 —— 清单 #1 ~ #8。

每个函数都用**独立的暴力实现**做对照，确认它算的确实是那个数学对象，
而不是「和另一个同样写错的函数自洽」。
"""

from __future__ import annotations

import math

import pytest

from svc.mathbase import (
    batch_root_factor,
    batch_root_factor_any,
    batch_root_factor_general,
    egcd,
    group_div,
    hash_prime,
    is_probable_prime,
    mod_inverse,
    multiexp,
    next_prime,
    prod,
    product_tree,
    shamir_trick,
    weighted_root_product,
)

# 一个够用的测试模数（不要求是 RSA 模数，只要求是合数/大数）
N = 0xE3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855
# 随便取一个与 N 互素的底数
G = 65547


# ---------------------------------------------------------------------------
# #1 is_probable_prime
# ---------------------------------------------------------------------------

class TestIsProbablePrime:
    @pytest.mark.parametrize("p", [2, 3, 5, 7, 11, 97, 7919, 104729, (1 << 61) - 1])
    def test_已知素数(self, p):
        assert is_probable_prime(p)

    @pytest.mark.parametrize(
        "c",
        [-7, -1, 0, 1, 4, 9, 15, 21, 100, 7917, 104730, 561, 1105, 1729, 41041],
    )
    def test_已知合数_含卡迈克尔数(self, c):
        # 561/1105/1729/41041 是卡迈克尔数：费马测试骗得过去，Miller-Rabin 骗不过
        assert not is_probable_prime(c)

    def test_大素数(self):
        # 2^127 - 1 是梅森素数
        assert is_probable_prime((1 << 127) - 1)

    def test_大合数(self):
        p, q = (1 << 61) - 1, (1 << 31) - 1
        assert not is_probable_prime(p * q)


class TestNextPrime:
    def test_基本性质(self):
        for start in (0, 1, 2, 3, 4, 100, 1000):
            p = next_prime(start)
            assert p >= max(start, 2)
            assert is_probable_prime(p)

    def test_不会漏掉更小的素数(self):
        # 区间 (start, p) 内不应再有素数
        for start in (10, 100, 1000):
            p = next_prime(start)
            assert not any(is_probable_prime(k) for k in range(max(start, 2), p))


# ---------------------------------------------------------------------------
# #2 hash_prime
# ---------------------------------------------------------------------------

class TestHashPrime:
    def test_结果是素数且位长正确(self):
        for out_bytes in (2, 4, 8, 16):
            p = hash_prime(b"hello", out_bytes)
            assert is_probable_prime(p)
            assert p.bit_length() == out_bytes * 8

    def test_确定性(self):
        assert hash_prime(b"abc", 8) == hash_prime(b"abc", 8)

    def test_不同输入基本不同(self):
        seen = {hash_prime(bytes([i]), 16) for i in range(16)}
        assert len(seen) == 16

    def test_out_bytes_太小时会碰撞(self):
        """这正是不建议用哈希版的原因 —— 顺手把它钉成一条测试。"""
        primes = [hash_prime(bytes([i]), 1) for i in range(64)]
        assert len(set(primes)) < len(primes), "1 字节只有 54 个素数，必然碰撞"

    def test_非法参数(self):
        with pytest.raises(ValueError):
            hash_prime(b"x", 0)


# ---------------------------------------------------------------------------
# #3 egcd
# ---------------------------------------------------------------------------

class TestEgcd:
    @pytest.mark.parametrize(
        "a,b",
        [(240, 46), (46, 240), (0, 5), (5, 0), (17, 17), (-240, 46), (240, -46)],
    )
    def test_恒等式(self, a, b):
        g, x, y = egcd(a, b)
        assert g == math.gcd(a, b)
        assert a * x + b * y == g


# ---------------------------------------------------------------------------
# #4 mod_inverse
# ---------------------------------------------------------------------------

class TestModInverse:
    def test_互素时可逆(self):
        for a in (3, 7, 11, 65537, G):
            inv = mod_inverse(a, N)
            assert a * inv % N == 1

    def test_不互素时抛异常(self):
        with pytest.raises(ValueError):
            mod_inverse(4, 8)

    def test_零没有逆(self):
        with pytest.raises(ValueError):
            mod_inverse(0, N)


# ---------------------------------------------------------------------------
# #5 group_div
# ---------------------------------------------------------------------------

class TestGroupDiv:
    def test_与乘法互逆(self):
        a, b = 12345, 67890
        assert group_div(a, b, N) * b % N == a % N

    def test_自除等于一(self):
        assert group_div(G, G, N) == 1

    def test_除零报错(self):
        with pytest.raises(ValueError):
            group_div(G, 0, N)


# ---------------------------------------------------------------------------
# #6 shamir_trick
# ---------------------------------------------------------------------------

class TestShamirTrick:
    def test_正确合并(self):
        """构造 g^(1/x)、g^(1/y)，合并后验算 (xy) 次方等于 g。"""
        x, y = 7, 11  # 互素
        # 先取一个底数 r，令 g = r^(x*y)，于是 g^(1/x) = r^y、g^(1/y) = r^x
        r = 1234567
        g = pow(r, x * y, N)
        root_x = pow(r, y, N)   # g^(1/x)
        root_y = pow(r, x, N)   # g^(1/y)

        merged = shamir_trick(root_x, root_y, x, y, N)
        assert merged is not None
        assert pow(merged, x * y, N) == g

    def test_同源自检(self):
        """两个根来自不同底数时必须拒绝，而不是硬算一个错值。"""
        x, y = 7, 11
        g1, g2 = 111, 222
        root_x = pow(pow(g1, 1, N), 1, N)
        root_y = pow(pow(g2, 1, N), 1, N)
        # 直接构造两个不同源的「根」
        rx = pow(3, y, N)       # 对应 g = 3^(xy)
        ry = pow(5, x, N)       # 对应 g = 5^(xy)
        assert shamir_trick(rx, ry, x, y, N) is None

    def test_不互素必须拒绝(self):
        """x、y 不互素时 Bézout 系数不是 1，硬算会静默出错，必须返回 None。"""
        x = y = 9
        r = 12345
        g = pow(r, x * y, N)
        root_x = pow(r, y, N)
        root_y = pow(r, x, N)
        assert shamir_trick(root_x, root_y, x, y, N) is None

    def test_同源但不互素(self):
        x, y = 6, 9  # gcd = 3
        r = 99
        # g^(1/x) 与 g^(1/y) 同源需要 g = r^(lcm(x,y))
        import math as _m

        L = x * y // _m.gcd(x, y)
        g = pow(r, L, N)
        root_x = pow(r, L // x, N)
        root_y = pow(r, L // y, N)
        assert shamir_trick(root_x, root_y, x, y, N) is None


# ---------------------------------------------------------------------------
# #7 multiexp
# ---------------------------------------------------------------------------

class TestMultiexp:
    @pytest.mark.parametrize("m", [1, 2, 3, 4, 8, 13])
    def test_与暴力实现一致(self, m):
        xs = [next_prime(1000 + 100 * i) for i in range(m)]
        alphas = [pow(G, 7 + i, N) for i in range(m)]

        X = prod(xs)
        expected = 1
        for a, x in zip(alphas, xs):
            expected = expected * pow(a, X // x, N) % N

        assert multiexp(alphas, xs, N) == expected

    def test_长度不匹配报错(self):
        with pytest.raises(ValueError):
            multiexp([1, 2], [3], N)

    def test_空输入(self):
        assert multiexp([], [], N) == 1


class TestWeightedRootProduct:
    @pytest.mark.parametrize("m", [1, 2, 3, 5, 8, 11])
    def test_与暴力实现一致(self, m):
        xs = [next_prime(2000 + 100 * i) for i in range(m)]
        ys = [3 * i + 1 for i in range(m)]

        X = prod(xs)
        expected = 1
        for y, x in zip(ys, xs):
            expected = expected * pow(pow(G, y, N), X // x, N) % N

        assert weighted_root_product(G, ys, xs, N) == expected


# ---------------------------------------------------------------------------
# #8 batch_root_factor
# ---------------------------------------------------------------------------

class TestBatchRootFactor:
    @pytest.mark.parametrize("m", [1, 2, 4, 8, 16])
    def test_2的幂_与暴力一致(self, m):
        xs = [next_prime(3000 + 100 * i) for i in range(m)]
        X = prod(xs)

        got = batch_root_factor(G, xs, N)
        expected = [pow(G, X // x, N) for x in xs]
        assert got == expected

    @pytest.mark.parametrize("m", [3, 5, 6, 7, 9, 11, 13, 15])
    def test_任意长度_与暴力一致(self, m):
        xs = [next_prime(4000 + 100 * i) for i in range(m)]
        X = prod(xs)

        got = batch_root_factor_any(G, xs, N)
        expected = [pow(G, X // x, N) for x in xs]
        assert got == expected

    def test_非2的幂长度会报错(self):
        with pytest.raises(ValueError):
            batch_root_factor(G, [3, 5, 7], N)

    def test_空输入(self):
        assert batch_root_factor(G, [], N) == []
        assert batch_root_factor_any(G, [], N) == []

    def test_分块版本(self):
        """chunk=2 时，每个输出对应「除该块之外全部之积」次方。"""
        xs = [3, 5, 7, 11]
        X = prod(xs)
        got = batch_root_factor_general(G, xs, 2, N)
        assert got == [
            pow(G, X // (xs[0] * xs[1]), N),
            pow(G, X // (xs[2] * xs[3]), N),
        ]


# ---------------------------------------------------------------------------
# 工具函数
# ---------------------------------------------------------------------------

class TestProduct:
    def test_prod(self):
        assert prod([]) == 1
        assert prod([2, 3, 5]) == 30

    def test_product_tree(self):
        assert product_tree([]) == 1
        assert product_tree([7]) == 7
        assert product_tree([2, 3, 5, 7, 11, 13]) == 30030
        assert product_tree(list(range(1, 51))) == math.factorial(50)
