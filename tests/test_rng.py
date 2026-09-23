"""随机源与「默认真随机」行为的测试。

**为什么单独立一个文件**：审计发现原来的默认种子全部写死在源码里
（``b"python-svc-v1"`` / ``b"svc-v1-setup"`` / ``b"vds-v2"`` / ``"web-demo"``）。
隐藏阶群方案的安全性前提是「没人知道模数 :math:`N` 的分解」，
而写死的种子让任何人都能重算出同一个 :math:`N`（进而分解它）——
该前提对演示来说并不成立。

改成「不传种子 = 真随机」之后，需要同时钉死两个方向的行为：

1. **不传种子** → 每次结果不同（这是安全性的那一半）；
2. **传了种子** → 完全可复现（这是实验可重复性的那一半，不能被改坏）。

两个方向都要测，只测一边的话，很容易在修另一边时把这一边弄丢。
"""

from __future__ import annotations

from svc import DeterministicRNG, setup
from vds import VDSSession
from vds.pos import pos_challenge

#: 测试用的最小合法参数（位长小 → 快）
BITS = 256
L = 8
N = 4


class TestDeterministicRNG:
    def test_不传种子时每次不同(self):
        a = DeterministicRNG().read_bytes(32)
        b = DeterministicRNG().read_bytes(32)
        assert a != b, "不传种子必须取真随机（os.urandom）"

    def test_不传种子时输出长度正确(self):
        assert len(DeterministicRNG().read_bytes(16)) == 16

    def test_bytes_种子可复现(self):
        a = DeterministicRNG(b"seed").read_bytes(32)
        b = DeterministicRNG(b"seed").read_bytes(32)
        assert a == b

    def test_str_种子可复现(self):
        a = DeterministicRNG("seed").read_bytes(32)
        b = DeterministicRNG(b"seed").read_bytes(32)
        assert a == b, "str 种子会先按 UTF-8 编码，应与等价 bytes 种子一致"

    def test_int_种子可复现(self):
        assert DeterministicRNG(7).read_bytes(32) == DeterministicRNG(7).read_bytes(32)

    def test_不同种子不同输出(self):
        assert DeterministicRNG(b"a").read_bytes(32) != DeterministicRNG(b"b").read_bytes(32)


class TestSetup默认随机:
    def test_不传_rng_两次给出不同参数(self):
        """默认路径必须是随机的 —— 否则 N 就被公开种子锁死了。"""
        a = setup(lambda_bits=16, l=L, n=N)
        b = setup(lambda_bits=16, l=L, n=N)
        assert a.N != b.N, "两次默认 setup 不该得到同一个模数"
        assert a.N.bit_length() == b.N.bit_length() == BITS

    def test_显式_rng_完全可复现(self):
        a = setup(lambda_bits=16, l=L, n=N, rng=DeterministicRNG(b"s"))
        b = setup(lambda_bits=16, l=L, n=N, rng=DeterministicRNG(b"s"))
        assert a.N == b.N and a.g == b.g, "给了同一个种子就必须一模一样"


class TestVDSSession默认随机:
    def test_不传_seed_两次给出不同模数(self):
        s1 = VDSSession(n_max=N, l=L * 2, lambda_bits=16, modulus_bits=BITS)
        s2 = VDSSession(n_max=N, l=L * 2, lambda_bits=16, modulus_bits=BITS)
        assert s1.crs.N != s2.crs.N

    def test_显式_seed_完全可复现(self):
        s1 = VDSSession(n_max=N, l=L * 2, lambda_bits=16, modulus_bits=BITS, seed=b"same")
        s2 = VDSSession(n_max=N, l=L * 2, lambda_bits=16, modulus_bits=BITS, seed=b"same")
        assert s1.crs.N == s2.crs.N and s1.crs.g == s2.crs.g


class TestPosChallenge默认随机:
    def test_不传_rng_两次给出不同挑战(self):
        a = pos_challenge(n=64, lambda_pos=8)
        b = pos_challenge(n=64, lambda_pos=8)
        assert a.indices != b.indices, "挑战必须不可预测，默认不能是固定序列"

    def test_显式_rng_可复现(self):
        rng1, rng2 = DeterministicRNG(b"s"), DeterministicRNG(b"s")
        assert pos_challenge(64, 8, rng1).indices == pos_challenge(64, 8, rng2).indices
