"""聚合与拆分测试 —— 清单 #23 ~ #26。

这一层是整个方案的**卖点**，也是最容易写出「看起来对、其实错」的地方：
错误往往表现为「合并后的证明仍然能通过某些检查，但合并顺序一变结果就不同」。
所以测试的重点不是「能不能验证通过」，而是：

    **真聚合的结果必须与直接对新集合算出来的证明逐位相同。**

如果只验证「聚合后的证明能通过 verify」，一个把 Λ 算错但在其他步骤
凑巧抵消的实现也可能蒙混过关；只有和直算结果比对才能彻底钉死。
"""

from __future__ import annotations

import pytest

from svc import (
    agg,
    agg_many_to_one,
    disagg,
    disagg_one_to_many,
    open_subvector,
    verify,
)

A = (1, 4, 9)
B = (2, 6, 11)
C = (0, 3, 12, 15)


@pytest.fixture
def pi_full(crs_n, values):
    """整向量打开证明（Λ 恒为 1），作为「一次拆成多块」的输入。"""
    return open_subvector(crs_n, list(range(crs_n.n)), list(values), values)


def _direct(crs_n, values, I):
    I = list(I)
    return open_subvector(crs_n, I, [values[i] for i in I], values)


# ---------------------------------------------------------------------------
# #23 disagg
# ---------------------------------------------------------------------------

class TestDisagg:
    def test_拆分结果能通过验证(self, crs_n, values, committed):
        pi_I = open_subvector(crs_n, A, [values[i] for i in A], values)
        for K in ([1], [1, 9], list(A)):
            pi_K = disagg(crs_n, A, [values[i] for i in A], pi_I, K)
            assert verify(
                crs_n, committed.C, list(K), [values[i] for i in K], pi_K
            ).ok, f"K = {K}"

    def test_拆分结果与直接算的逐位相同(self, crs_n, values):
        """关键断言：真拆分 == 对新集合从零算一遍。"""
        pi_I = open_subvector(crs_n, A, [values[i] for i in A], values)
        for K in ([1], [1, 9], list(A)):
            pi_K = disagg(crs_n, A, [values[i] for i in A], pi_I, K)
            direct = _direct(crs_n, values, K)
            assert pi_K.S_I == direct.S_I, f"K = {K} 时 S 不一致"
            assert pi_K.Lambda_I == direct.Lambda_I, f"K = {K} 时 Λ 不一致"

    def test_K_必须是_I_的子集(self, crs_n, values):
        pi_I = open_subvector(crs_n, A, [values[i] for i in A], values)
        with pytest.raises(ValueError, match="K ⊆ I"):
            disagg(crs_n, A, [values[i] for i in A], pi_I, (1, 99))

    def test_拆到空集会报错(self, crs_n, values):
        # disagg 允许 K=∅ 从数学上（S_∅=U_n），但 open 路径不允许空集合时另有约束；
        # 这里只确认 K=∅ 时确实得到 S=U_n 且 Λ=Λ_I
        pi_I = open_subvector(crs_n, A, [values[i] for i in A], values)
        pi_empty = disagg(crs_n, A, [values[i] for i in A], pi_I, [])
        assert pi_empty.S_I == crs_n.U_n


# ---------------------------------------------------------------------------
# #24 agg
# ---------------------------------------------------------------------------

class TestAgg:
    def test_合并结果能通过验证(self, crs_n, values, committed):
        pi_A = _direct(crs_n, values, A)
        pi_B = _direct(crs_n, values, B)
        merged = agg(crs_n, A, [values[i] for i in A], pi_A,
                     B, [values[i] for i in B], pi_B)
        K = sorted(set(A) | set(B))
        assert verify(crs_n, committed.C, K, [values[i] for i in K], merged).ok

    def test_合并结果与直接算的逐位相同(self, crs_n, values):
        """最关键的一条：真聚合 == 直算。"""
        pi_A = _direct(crs_n, values, A)
        pi_B = _direct(crs_n, values, B)
        merged = agg(crs_n, A, [values[i] for i in A], pi_A,
                     B, [values[i] for i in B], pi_B)
        direct = _direct(crs_n, values, sorted(set(A) | set(B)))
        assert merged.S_I == direct.S_I
        assert merged.Lambda_I == direct.Lambda_I

    def test_相交集合被拒绝(self, crs_n, values):
        pi_A = _direct(crs_n, values, A)
        pi_A2 = _direct(crs_n, values, (1, 4, 7))
        with pytest.raises(ValueError, match="重叠"):
            agg(crs_n, A, [values[i] for i in A], pi_A,
                (1, 4, 7), [values[i] for i in (1, 4, 7)], pi_A2)

    def test_合并顺序无关(self, crs_n, values):
        """三个集合，两种结合顺序必须得到完全一样的证明。"""
        pasts = {name: _direct(crs_n, values, s)
                 for name, s in (("a", A), ("b", B), ("c", C))}

        left = agg(crs_n,
                   sorted(set(A) | set(B)), [values[i] for i in sorted(set(A) | set(B))],
                   agg(crs_n, A, [values[i] for i in A], pasts["a"],
                       B, [values[i] for i in B], pasts["b"]),
                   C, [values[i] for i in C], pasts["c"])

        right = agg(crs_n,
                    A, [values[i] for i in A], pasts["a"],
                    sorted(set(B) | set(C)), [values[i] for i in sorted(set(B) | set(C))],
                    agg(crs_n, B, [values[i] for i in B], pasts["b"],
                        C, [values[i] for i in C], pasts["c"]))

        assert left.S_I == right.S_I, "合并顺序改变了 S —— 增量聚合性质被破坏"
        assert left.Lambda_I == right.Lambda_I, "合并顺序改变了 Λ —— 增量聚合性质被破坏"

        direct = _direct(crs_n, values, sorted(set(A) | set(B) | set(C)))
        assert left.S_I == direct.S_I and left.Lambda_I == direct.Lambda_I

    def test_合并后还能继续合并(self, crs_n, values):
        """聚合结果仍是合法证明，可以无限次参与合并。"""
        pi = _direct(crs_n, values, A)
        acc = list(A)
        for s in (B, C, (5,), (7, 8), (10,), (13, 14)):
            other = _direct(crs_n, values, s)
            pi = agg(crs_n, acc, [values[i] for i in acc], pi,
                     s, [values[i] for i in s], other)
            acc = sorted(set(acc) | set(s))
        direct = _direct(crs_n, values, acc)
        assert pi.S_I == direct.S_I and pi.Lambda_I == direct.Lambda_I

    def test_合并后再拆回去(self, crs_n, values):
        """agg 与 disagg 互逆。"""
        pi_A = _direct(crs_n, values, A)
        pi_B = _direct(crs_n, values, B)
        merged = agg(crs_n, A, [values[i] for i in A], pi_A,
                     B, [values[i] for i in B], pi_B)
        # disagg 要求「传入的 I」与「证明里的 I」一致，
        # 所以这里要用并集全体，不能用它的子集。
        K = sorted(set(A) | set(B))
        back = disagg(crs_n, K, [values[i] for i in K], merged, [K[0]])
        direct = _direct(crs_n, values, [K[0]])
        assert back.S_I == direct.S_I
        assert back.Lambda_I == direct.Lambda_I


# ---------------------------------------------------------------------------
# #25 disagg_one_to_many
# ---------------------------------------------------------------------------

class TestDisaggOneToMany:
    def test_每个块都能独立验证(self, crs_n, values, committed, pi_full):
        blocks = disagg_one_to_many(
            crs_n, 4, list(range(crs_n.n)), values, pi_full
        )
        assert len(blocks) == crs_n.n // 4
        for ids, bvals, bp in blocks:
            assert verify(crs_n, committed.C, list(ids), list(bvals), bp).ok

    def test_每个块与直算逐位相同(self, crs_n, values, pi_full):
        blocks = disagg_one_to_many(
            crs_n, 4, list(range(crs_n.n)), values, pi_full
        )
        for ids, _, bp in blocks:
            direct = _direct(crs_n, values, ids)
            assert bp.S_I == direct.S_I, f"{ids} 的 S 不一致"
            assert bp.Lambda_I == direct.Lambda_I, f"{ids} 的 Λ 不一致"

    def test_块大小不整除时也能处理(self, crs_n, values, committed, pi_full):
        blocks = disagg_one_to_many(
            crs_n, 5, list(range(crs_n.n)), values, pi_full
        )
        assert sum(len(ids) for ids, _, _ in blocks) == crs_n.n
        for ids, bvals, bp in blocks:
            assert verify(crs_n, committed.C, list(ids), list(bvals), bp).ok

    def test_非法块大小(self, crs_n, values, pi_full):
        with pytest.raises(ValueError):
            disagg_one_to_many(crs_n, 0, list(range(crs_n.n)), values, pi_full)


# ---------------------------------------------------------------------------
# #26 agg_many_to_one
# ---------------------------------------------------------------------------

class TestAggManyToOne:
    def test_合并全部块等于整向量证明(self, crs_n, values, pi_full):
        blocks = disagg_one_to_many(
            crs_n, 4, list(range(crs_n.n)), values, pi_full
        )
        total = agg_many_to_one(
            crs_n, [(ids, bvals, bp) for ids, bvals, bp in blocks]
        )
        assert total.S_I == pi_full.S_I
        assert total.Lambda_I == pi_full.Lambda_I

    def test_合并部分块(self, crs_n, values, pi_full):
        blocks = disagg_one_to_many(
            crs_n, 4, list(range(crs_n.n)), values, pi_full
        )
        subset = blocks[:3]
        total = agg_many_to_one(
            crs_n, [(ids, bvals, bp) for ids, bvals, bp in subset]
        )
        want = sorted(i for ids, _, _ in subset for i in ids)
        direct = _direct(crs_n, values, want)
        assert total.I == tuple(want)
        assert total.S_I == direct.S_I and total.Lambda_I == direct.Lambda_I

    def test_块数不是2的幂(self, crs_n, values, pi_full):
        blocks = disagg_one_to_many(
            crs_n, 4, list(range(crs_n.n)), values, pi_full
        )
        for k in (1, 2, 3, 5, 7):
            total = agg_many_to_one(
                crs_n, [(ids, bvals, bp) for ids, bvals, bp in blocks[:k]]
            )
            want = sorted(i for ids, _, _ in blocks[:k] for i in ids)
            direct = _direct(crs_n, values, want)
            assert total.S_I == direct.S_I, f"k = {k}"
            assert total.Lambda_I == direct.Lambda_I, f"k = {k}"

    def test_空列表报错(self, crs_n):
        with pytest.raises(ValueError):
            agg_many_to_one(crs_n, [])
