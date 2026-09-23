"""核心抽象测试：``d(v \\ I) = (S, Λ)``。

这一层来自 Catalano-Fiore 方案的另一种叙述方式：

* **证明就是摘要** —— ``π_I = d(v \\ I)``，于是 ``commit`` 与 ``open``
  是同一个函数在两个不同 ``excluded`` 下的取值；
* **顺序「加回」** —— 拆分、验证、追加新位置都归结为
  ``(S, Λ) ← (S^{e_i}, Λ^{e_i}·S^{v_i})`` 循环若干次。

这些测试的价值在于：它们把「统一」这件事**钉死成可检查的等式** ——
如果哪天有人把 `commit` 或 `open` 改得偏离了这个抽象，这里会立刻红。
"""

from __future__ import annotations

import pytest

from svc import (
    DeterministicRNG,
    Opening,
    VerifyCode,
    add_back,
    commit,
    digest_of,
    disagg,
    disagg_one_to_many,
    open_subvector,
    setup,
    specialize,
    verify,
)

I_SAMPLE = (1, 4, 9)
#: 中等大小的集合（15 个位置）与全部位置（30 个），用来验证「加回」在大 |I| 下也对
I_MEDIUM = tuple(range(0, 30, 2))
I_BIG = tuple(range(30))


@pytest.fixture(scope="module")
def crs32():
    """30 个位置的小会话（模数取小，跑得快）。"""
    rng = DeterministicRNG(b"core-abstraction")
    c = setup(lambda_bits=16, l=16, n=30, rng=rng, modulus_bits=256)
    return c


@pytest.fixture(scope="module")
def vals32(crs32):
    rng = DeterministicRNG(b"core-values")
    return tuple(rng.randbelow(1 << 16) for _ in range(30))


@pytest.fixture(scope="module")
def sn32(crs32):
    return specialize(crs32, 30)


# ---------------------------------------------------------------------------
# digest_of：承诺与打开是同一个函数
# ---------------------------------------------------------------------------

class TestDigestOfUnifiesCommitAndOpen:
    def test_去掉空集就是承诺(self, sn32, vals32):
        d = digest_of(sn32, vals32)
        com = commit(sn32, vals32)
        assert d.S == sn32.U_n, "S 分量应当就是累加器 U_n"
        assert d.Lambda == com.C, "Λ 分量应当就是承诺 C"

    def test_去掉_I_就是打开证明(self, sn32, vals32):
        for I in ([0], I_SAMPLE, (2, 3), tuple(range(30))):
            d = digest_of(sn32, vals32, I)
            pi = open_subvector(
                sn32, list(I), [vals32[i] for i in I], vals32
            )
            assert d.S == pi.S_I, f"I = {I} 的 S 不一致"
            assert d.Lambda == pi.Lambda_I, f"I = {I} 的 Λ 不一致"

    def test_去掉全集是平凡摘要(self, sn32, vals32):
        """d(v \\ [n]) = (g^{e_∅}, 空乘积) = (g, 1)。"""
        d = digest_of(sn32, vals32, tuple(range(30)))
        assert d.S == sn32.g
        assert d.Lambda == 1

    def test_Opending_digest_视图往返(self, sn32, vals32):
        pi = open_subvector(sn32, I_SAMPLE, [vals32[i] for i in I_SAMPLE], vals32)
        assert Opening.from_digest(pi.digest, I_SAMPLE) == pi

    def test_长度不符报错(self, sn32, vals32):
        with pytest.raises(ValueError, match="长度"):
            digest_of(sn32, vals32[:10])


# ---------------------------------------------------------------------------
# add_back：加回一个位置
# ---------------------------------------------------------------------------

class TestAddBack:
    def test_加回一个位置等于对更小集合取摘要(self, sn32, vals32):
        """从 d(v \\ {i}) 加回 i，应当得到 d(v \\ ∅) = (U_n, C)。"""
        for i in (0, 7, 29):
            d = digest_of(sn32, vals32, (i,))
            S, Lam = add_back(
                d.S, d.Lambda, sn32.crs.primegen.get(i), vals32[i], sn32.N
            )
            full = digest_of(sn32, vals32)
            assert S == full.S, f"i = {i} 时 S 不对"
            assert Lam == full.Lambda, f"i = {i} 时 Λ 不对"

    def test_加回顺序无关(self, sn32, vals32):
        """逐个加回的结果必须与顺序无关 —— 否则拆分/验证都会依赖下标遍历次序。"""
        I = (2, 5, 11, 17)
        start = digest_of(sn32, vals32, I)
        pg, N = sn32.crs.primegen, sn32.N

        results = []
        for order in ([2, 5, 11, 17], [17, 11, 5, 2], [5, 17, 2, 11]):
            S, Lam = start.S, start.Lambda
            for i in order:
                S, Lam = add_back(S, Lam, pg.get(i), vals32[i], N)
            results.append((S, Lam))

        assert len(set(results)) == 1, "不同加回顺序得到了不同结果"
        assert results[0] == (digest_of(sn32, vals32).S,
                              digest_of(sn32, vals32).Lambda)

    def test_加回全部位置得到d_v(self, sn32, vals32):
        I = tuple(range(30))
        start = digest_of(sn32, vals32, I)      # = (g, 1)
        S, Lam = start.S, start.Lambda
        for i in I:
            S, Lam = add_back(
                S, Lam, sn32.crs.primegen.get(i), vals32[i], sn32.N
            )
        full = digest_of(sn32, vals32)
        assert (S, Lam) == (full.S, full.Lambda)


# ---------------------------------------------------------------------------
# verify：用「加回」实现
# ---------------------------------------------------------------------------

class TestVerifyByAddBack:
    def test_大集合也能正确验证(self, sn32, vals32):
        """|I| 很大时也要对 —— 这是重写 verify 的动机之一。"""
        for I in (I_MEDIUM, I_BIG):
            pi = open_subvector(
                sn32, list(I), [vals32[i] for i in I], vals32
            )
            com = commit(sn32, vals32)
            assert verify(
                sn32, com.C, list(I), [vals32[i] for i in I], pi
            ).ok, f"I 大小 {len(I)} 验证失败"

    def test_与加回结果一致(self, sn32, vals32):
        """verify 的接受条件就是「加回后正好变回 d(v)」。"""
        com = commit(sn32, vals32)
        d_full = digest_of(sn32, vals32)
        assert com.C == d_full.Lambda and sn32.U_n == d_full.S

        I = I_SAMPLE
        pi = open_subvector(sn32, list(I), [vals32[i] for i in I], vals32)
        S, Lam = pi.S_I, pi.Lambda_I
        for i in I:
            S, Lam = add_back(
                S, Lam, sn32.crs.primegen.get(i), vals32[i], sn32.N
            )
        assert (S, Lam) == (d_full.S, d_full.Lambda)
        assert verify(sn32, com.C, list(I), [vals32[i] for i in I], pi).ok

    def test_失败环节仍然分得清(self, sn32, vals32):
        com = commit(sn32, vals32)
        I = I_SAMPLE
        vals_I = [vals32[i] for i in I]
        pi = open_subvector(sn32, list(I), vals_I, vals32)

        # 伪造 S_I → BAD_S_I
        forged = Opening((pi.S_I * 7) % sn32.N, pi.Lambda_I, pi.I)
        r = verify(sn32, com.C, list(I), vals_I, forged)
        assert r.code is VerifyCode.BAD_S_I

        # 值骗人 → BAD_LAMBDA
        lying = list(vals_I)
        lying[0] += 1
        r = verify(sn32, com.C, list(I), lying, pi)
        assert r.code is VerifyCode.BAD_LAMBDA


# ---------------------------------------------------------------------------
# disagg：用「加回」实现，结果必须等于直接取摘要
# ---------------------------------------------------------------------------

class TestDisaggEqualsDigestOf:
    def test_拆分结果就是子集合的摘要(self, sn32, vals32):
        """关键等式：disagg(d(v\\I), K) == d(v\\K)。"""
        I = tuple(range(0, 20, 3))      # (0,3,6,9,12,15,18)
        pi = open_subvector(sn32, list(I), [vals32[i] for i in I], vals32)

        for K in ([0], [3, 9], [0, 3, 6, 9, 12, 15, 18], [15, 18]):
            got = disagg(sn32, list(I), [vals32[i] for i in I], pi, K)
            want = digest_of(sn32, vals32, K)
            assert got.S_I == want.S, f"K = {K} 的 S 不对"
            assert got.Lambda_I == want.Lambda, f"K = {K} 的 Λ 不对"

    def test_拆到全集是恒等(self, sn32, vals32):
        I = (1, 4, 9)
        pi = open_subvector(sn32, list(I), [vals32[i] for i in I], vals32)
        same = disagg(sn32, list(I), [vals32[i] for i in I], pi, I)
        assert (same.S_I, same.Lambda_I) == (pi.S_I, pi.Lambda_I)


# ---------------------------------------------------------------------------
# disagg_one_to_many：递归二分
# ---------------------------------------------------------------------------

class TestRecursiveSplit:
    @pytest.mark.parametrize("B", [1, 2, 3, 5, 8])
    def test_每块的摘要都正确(self, sn32, vals32, B):
        idx = list(range(30))
        pi_full = digest_of(sn32, vals32, idx)
        blocks = disagg_one_to_many(
            sn32, B, idx, vals32, Opening.from_digest(pi_full, idx)
        )
        assert sum(len(ids) for ids, _, _ in blocks) == 30
        assert sorted(i for ids, _, _ in blocks for i in ids) == idx

        for ids, bvals, bp in blocks:
            want = digest_of(sn32, vals32, ids)
            assert bp.S_I == want.S, f"块 {ids} 的 S 不对"
            assert bp.Lambda_I == want.Lambda, f"块 {ids} 的 Λ 不对"
            assert bvals == tuple(vals32[i] for i in ids)

    def test_每块都能通过验证(self, sn32, vals32):
        com = commit(sn32, vals32)
        idx = list(range(30))
        pi_full = digest_of(sn32, vals32, idx)
        blocks = disagg_one_to_many(
            sn32, 4, idx, vals32, Opening.from_digest(pi_full, idx)
        )
        for ids, bvals, bp in blocks:
            assert verify(sn32, com.C, list(ids), list(bvals), bp).ok

    def test_块大小大于总数时退化为一块(self, sn32, vals32):
        idx = list(range(30))
        pi_full = digest_of(sn32, vals32, idx)
        blocks = disagg_one_to_many(
            sn32, 1000, idx, vals32, Opening.from_digest(pi_full, idx)
        )
        assert len(blocks) == 1
        assert blocks[0][0] == tuple(idx)

    def test_空集合(self, sn32, vals32):
        empty = digest_of(sn32, vals32, ())
        blocks = disagg_one_to_many(sn32, 4, [], vals32, Opening.from_digest(empty))
        assert blocks == []

    def test_非法块大小(self, sn32, vals32):
        idx = list(range(30))
        pi_full = digest_of(sn32, vals32, idx)
        with pytest.raises(ValueError):
            disagg_one_to_many(sn32, 0, idx, vals32, Opening.from_digest(pi_full, idx))
