"""§4.2 的 ``VC.PPCom`` / ``VC.FastOpen`` 测试。

重点有三条：

1. **等价性** —— ``FastOpen`` 出来的证明必须能过 ``verify``，
   且与直接 ``Open`` 得到的证明在验证结果上无差别；
2. **块划分** —— ``covering_blocks`` 必须给出最小覆盖，
   ``|S|`` 不超过 ``|I|`` 也不超过块数；
3. **代价形状** —— 建议大小按 ``(n/B)·|π|`` 走，``B = n`` 时只剩 1 块。
"""

from __future__ import annotations

import pytest

from svc import (
    DeterministicRNG,
    commit,
    open_subvector,
    setup,
    specialize,
    verify,
)
from svc.fastopen import (
    Precomputed,
    blocks_of,
    covering_blocks,
    fast_open,
    ppcom,
)

N = 64
L = 32
MODULUS_BITS = 256


@pytest.fixture(scope="module")
def crs_n():
    rng = DeterministicRNG(b"pytest-fastopen")
    crs = setup(lambda_bits=16, l=L, n=N, rng=rng, modulus_bits=MODULUS_BITS)
    return specialize(crs, N)


@pytest.fixture(scope="module")
def vals():
    rng = DeterministicRNG(b"pytest-fastopen-vals")
    return tuple(rng.randbelow(1 << L) for _ in range(N))


@pytest.fixture(scope="module")
def C(crs_n, vals):
    return commit(crs_n, vals).C


# ---------------------------------------------------------------------------
# 块划分
# ---------------------------------------------------------------------------

class TestBlocks:
    def test_整除时块数(self):
        assert blocks_of(12, 4) == [(0, 1, 2, 3), (4, 5, 6, 7), (8, 9, 10, 11)]

    def test_不整除时末块更短(self):
        blocks = blocks_of(10, 4)
        assert blocks == [(0, 1, 2, 3), (4, 5, 6, 7), (8, 9)]
        assert len(blocks) == 3

    def test_B_等于_n_时只有一块(self):
        assert blocks_of(5, 5) == [(0, 1, 2, 3, 4)]
        assert blocks_of(5, 99) == [(0, 1, 2, 3, 4)]

    def test_B_为1_时每块单点(self):
        assert blocks_of(4, 1) == [(0,), (1,), (2,), (3,)]

    def test_块覆盖全部下标且互不相交(self):
        blocks = blocks_of(23, 5)
        flat = [i for b in blocks for i in b]
        assert flat == list(range(23))          # 顺序铺满
        assert len(set(flat)) == len(flat)      # 无重复

    @pytest.mark.parametrize("n,b", [(0, 4), (4, 0), (-1, 4), (4, -1)])
    def test_非法输入(self, n, b):
        with pytest.raises(ValueError):
            blocks_of(n, b)

    def test_最小覆盖(self):
        assert covering_blocks([0, 1, 4, 9], 3) == [0, 1, 3]
        assert covering_blocks([2], 8) == [0]
        assert covering_blocks([8], 8) == [1]

    def test_覆盖块数不超过下标数(self):
        I = [0, 3, 4, 7, 8]
        assert len(covering_blocks(I, 4)) <= len(I)

    def test_覆盖的块确实包含全部下标(self):
        B, I = 5, [1, 4, 5, 11, 17]
        blocks = blocks_of(23, B)
        covered = {i for j in covering_blocks(I, B) for i in blocks[j]}
        assert set(I) <= covered


# ---------------------------------------------------------------------------
# PPCom
# ---------------------------------------------------------------------------

class TestPPCom:
    def test_块数与建议大小随B变化(self, crs_n, vals):
        prev_bits = None
        for B in (64, 32, 16, 8, 4):
            _, aux = ppcom(crs_n, B, vals)
            assert aux.n_blocks == -(-N // B)
            assert aux.n == N and aux.B == B
            # 块越细，建议越大（B 减半则块数翻倍）
            if prev_bits is not None:
                assert aux.advice_bits >= prev_bits
            prev_bits = aux.advice_bits

    def test_承诺与直接commit一致(self, crs_n, vals, C):
        C2, _ = ppcom(crs_n, 8, vals)
        assert C2 == C

    def test_每块的证明都能自证(self, crs_n, vals, C):
        _, aux = ppcom(crs_n, 8, vals)
        for j, blk in enumerate(aux.proofs):
            idx = aux.block_indices(j)
            assert blk.I == idx
            assert verify(crs_n, C, list(idx), [vals[i] for i in idx], blk).ok

    def test_B_等于_n_时只有一块且就是全量证明(self, crs_n, vals, C):
        _, aux = ppcom(crs_n, N, vals)
        assert aux.n_blocks == 1
        # 全量证明退化成 (g, 1)
        assert aux.proofs[0].S_I == crs_n.crs.g
        assert aux.proofs[0].Lambda_I == 1

    @pytest.mark.parametrize("B", [0, -1])
    def test_非法B(self, crs_n, vals, B):
        with pytest.raises(ValueError):
            ppcom(crs_n, B, vals)

    def test_B_超过n(self, crs_n, vals):
        with pytest.raises(ValueError):
            ppcom(crs_n, N + 1, vals)

    def test_空向量(self, crs_n):
        with pytest.raises(ValueError):
            ppcom(crs_n, 4, [])

    def test_返回的Precomputed带原始向量(self, crs_n, vals):
        _, aux = ppcom(crs_n, 8, vals)
        assert isinstance(aux, Precomputed)
        assert aux.values == tuple(vals)


# ---------------------------------------------------------------------------
# FastOpen
# ---------------------------------------------------------------------------

class TestFastOpen:
    CASES = [
        [0],
        [0, 1],
        [3, 4, 5],
        [0, 7, 8, 63],
        [5, 6, 7, 8, 9],
        list(range(N)),
        [1, 17, 33, 49],
    ]

    @pytest.mark.parametrize("B", [1, 2, 4, 8, 16, 64])
    def test_各种B下都能验证通过(self, crs_n, vals, C, B):
        _, aux = ppcom(crs_n, B, vals)
        for I in self.CASES:
            pi = fast_open(crs_n, aux, I)
            report = verify(crs_n, C, I, [vals[i] for i in I], pi)
            assert report.ok, f"B={B} I={I} 失败于 {report.code.name}"

    @pytest.mark.parametrize("B", [1, 4, 16])
    def test_与直接Open在验证上等价(self, crs_n, vals, C, B):
        _, aux = ppcom(crs_n, B, vals)
        for I in self.CASES:
            fast = verify(crs_n, C, I, [vals[i] for i in I], fast_open(crs_n, aux, I))
            slow = verify(
                crs_n, C, I, [vals[i] for i in I],
                open_subvector(crs_n, I, [vals[i] for i in I], vals),
            )
            assert fast.ok == slow.ok is True

    def test_证明里的下标与请求一致(self, crs_n, vals):
        _, aux = ppcom(crs_n, 8, vals)
        for I in self.CASES:
            assert fast_open(crs_n, aux, I).I == tuple(sorted(I))

    def test_整块命中时直接复用块证明(self, crs_n, vals):
        _, aux = ppcom(crs_n, 8, vals)
        # I 恰好是第 2 块，应该原样返回 π_2（不需要 disagg）
        pi = fast_open(crs_n, aux, aux.block_indices(2))
        assert pi.S_I == aux.proofs[2].S_I
        assert pi.Lambda_I == aux.proofs[2].Lambda_I

    def test_乱序输入会被规范化(self, crs_n, vals, C):
        _, aux = ppcom(crs_n, 8, vals)
        pi = fast_open(crs_n, aux, [9, 1, 5])
        assert pi.I == (1, 5, 9)
        # 值必须跟着规范化后的下标走
        assert verify(crs_n, C, list(pi.I), [vals[i] for i in pi.I], pi).ok

    def test_重复下标(self, crs_n, vals, C):
        _, aux = ppcom(crs_n, 8, vals)
        pi = fast_open(crs_n, aux, [3, 3, 3])
        assert pi.I == (3,)
        assert verify(crs_n, C, [3], [vals[3]], pi).ok

    def test_空集合报错(self, crs_n, vals):
        _, aux = ppcom(crs_n, 8, vals)
        with pytest.raises(ValueError):
            fast_open(crs_n, aux, [])

    def test_越界报错(self, crs_n, vals):
        _, aux = ppcom(crs_n, 8, vals)
        with pytest.raises(ValueError):
            fast_open(crs_n, aux, [N])

    def test_多个子集可以复用同一份建议(self, crs_n, vals, C):
        _, aux = ppcom(crs_n, 8, vals)
        for I in ([2, 3], [18, 19], [30], [40, 41, 42, 43]):
            assert verify(crs_n, C, I, [vals[i] for i in I], fast_open(crs_n, aux, I)).ok
