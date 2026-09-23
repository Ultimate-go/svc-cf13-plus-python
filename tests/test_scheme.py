"""方案中间量与本体测试 —— 清单 #12 ~ #22。

重点验证三类东西：

1. **定义一致性**：:math:`S_i`、:math:`S_I`、:math:`S_I^{e_I} = U_n` 这些
   恒等式是否真的成立（拿定义式独立算一遍对照）。
2. **双路径一致**：批处理路径（分治）与朴素路径（逐项）必须**逐位相同**。
   清单 PS 说「前期使用 13 进行 debug，这里的 8 算大量内容更快」——
   两条路互为验证，谁写错了立刻暴露。
3. **失败必须被区分**：:class:`~svc.VerifyCode` 要指出具体哪一步挂了。
"""

from __future__ import annotations

import pytest

from svc import (
    DeterministicRNG,
    VerifyCode,
    commit,
    e_of,
    lambda_subset,
    open_subvector,
    product_tree,
    reconstruct_s_i,
    s_iota,
    s_partial_root,
    s_subset,
    setup,
    specialize,
    verify,
)

I_SAMPLE = (1, 4, 9)


# ---------------------------------------------------------------------------
# #12 e_of
# ---------------------------------------------------------------------------

class TestEOf:
    def test_等于素数的连乘(self, crs, crs_n):
        pg = crs.primegen
        for I in ([0], [0, 1], [2, 5, 7], list(range(16))):
            assert e_of(pg, I) == product_tree([pg.get(i) for i in I])

    def test_空集为一(self, crs):
        assert e_of(crs.primegen, []) == 1

    def test_整除关系(self, crs_n):
        """e_I 必须整除 e_[n]，这是「不需要开方」的前提。"""
        for I in ([0], [1, 2], [0, 3, 7], list(range(16))):
            assert crs_n.e_all % e_of(crs_n.crs.primegen, I) == 0


# ---------------------------------------------------------------------------
# #13 ~ #15 中间量
# ---------------------------------------------------------------------------

class TestMidValues:
    def test_s_iota_定义式(self, crs_n):
        pg = crs_n.crs.primegen
        for i in (0, 5, 15):
            e_i = pg.get(i)
            assert s_iota(crs_n.g, crs_n.e_all, e_i, crs_n.N) == pow(
                crs_n.g, crs_n.e_all // e_i, crs_n.N
            )

    def test_s_subset_定义式(self, crs_n):
        e_I = e_of(crs_n.crs.primegen, I_SAMPLE)
        assert s_subset(crs_n.g, crs_n.e_all, e_I, crs_n.N) == pow(
            crs_n.g, crs_n.e_all // e_I, crs_n.N
        )

    def test_S_I_的_e_I_次方等于_U_n(self, crs_n):
        """论文验证第一步的恒等式，必须在正确构造下成立。"""
        for I in ([0], I_SAMPLE, list(range(16))):
            e_I = e_of(crs_n.crs.primegen, I)
            S_I = s_subset(crs_n.g, crs_n.e_all, e_I, crs_n.N)
            assert pow(S_I, e_I, crs_n.N) == crs_n.U_n

    def test_s_partial_root_定义式(self, crs_n):
        pg = crs_n.crs.primegen
        e_I = e_of(pg, I_SAMPLE)
        for j in (0, 3, 15):  # j ∉ I
            assert s_partial_root(
                crs_n.g, crs_n.e_all, e_I, pg.get(j), crs_n.N
            ) == pow(crs_n.g, crs_n.e_all // (pg.get(j) * e_I), crs_n.N)

    def test_s_partial_root_在_j_属于_I_时必须报错(self, crs_n):
        """``j ∈ I`` 时 e_j·e_I 不整除 e_[n]（e_j 会出现两次），代数上求不出根。"""
        pg = crs_n.crs.primegen
        e_I = e_of(pg, I_SAMPLE)
        with pytest.raises(ValueError, match="不整除"):
            s_partial_root(crs_n.g, crs_n.e_all, e_I, pg.get(I_SAMPLE[0]), crs_n.N)

    def test_s_iota_下标越界时报错(self, crs_n):
        with pytest.raises(ValueError, match="不整除"):
            s_iota(crs_n.g, crs_n.e_all, 7919, crs_n.N)  # 7919 不是这一组素数


# ---------------------------------------------------------------------------
# #16 reconstruct_s_i
# ---------------------------------------------------------------------------

class TestReconstruct:
    def test_重构结果等于直接算的_S_i(self, crs_n):
        pg = crs_n.crs.primegen
        e_I = e_of(pg, I_SAMPLE)
        S_I = s_subset(crs_n.g, crs_n.e_all, e_I, crs_n.N)

        for i in I_SAMPLE:
            expect = s_iota(crs_n.g, crs_n.e_all, pg.get(i), crs_n.N)
            assert reconstruct_s_i(S_I, I_SAMPLE, i, pg, crs_n.N) == expect

    def test_下标不在集合里时报错(self, crs_n):
        pg = crs_n.crs.primegen
        S_I = s_subset(
            crs_n.g, crs_n.e_all, e_of(pg, I_SAMPLE), crs_n.N
        )
        with pytest.raises(ValueError, match="不在集合"):
            reconstruct_s_i(S_I, I_SAMPLE, 2, pg, crs_n.N)


# ---------------------------------------------------------------------------
# #17 lambda_subset
# ---------------------------------------------------------------------------

class TestLambdaSubset:
    def test_批处理与朴素路径逐位相同(self, crs_n, values):
        """双路径一致性 —— 这是发现「分治写错」最有效的一条测试。"""
        pg = crs_n.crs.primegen
        for I in ([0], I_SAMPLE, [15], list(range(16))):
            fast = lambda_subset(
                crs_n.g, crs_n.e_all, I, values, crs_n.N, pg, crs_n.n,
                use_batch=True,
            )
            slow = lambda_subset(
                crs_n.g, crs_n.e_all, I, values, crs_n.N, pg, crs_n.n,
                use_batch=False,
            )
            assert fast == slow, f"I = {I} 时两条路径不一致"

    def test_打开整个向量时为空乘积(self, crs_n, values):
        """I = [n] 时 ∏ 为空，Λ 应为 1。"""
        got = lambda_subset(
            crs_n.g, crs_n.e_all, list(range(crs_n.n)), values,
            crs_n.N, crs_n.crs.primegen, crs_n.n,
        )
        assert got == 1

    def test_满足定义式(self, crs_n, values):
        """Λ_I^{e_I} 应等于 ∏_{j∉I} S_j^{y_j}。"""
        pg = crs_n.crs.primegen
        e_I = e_of(pg, I_SAMPLE)
        Lam = lambda_subset(
            crs_n.g, crs_n.e_all, I_SAMPLE, values, crs_n.N, pg, crs_n.n
        )
        rhs = 1
        for j in range(crs_n.n):
            if j in I_SAMPLE:
                continue
            S_j = s_iota(crs_n.g, crs_n.e_all, pg.get(j), crs_n.N)
            rhs = rhs * pow(S_j, values[j], crs_n.N) % crs_n.N
        assert pow(Lam, e_I, crs_n.N) == rhs


# ---------------------------------------------------------------------------
# #18 ~ #19 setup / specialize
# ---------------------------------------------------------------------------

class TestSetupSpecialize:
    def test_setup_的_CRS_字段(self, crs):
        assert crs.N.bit_length() == 256
        assert 1 <= crs.g < crs.N
        assert crs.l == 16
        assert crs.primegen.max_sz == 16

    def test_modulus_bits_默认值(self):
        # 显式给种子：默认路径现在是随机的，测试要的是「位长公式」这一条性质
        c = setup(lambda_bits=32, l=8, n=4, rng=DeterministicRNG(b"modbits"))
        assert c.N.bit_length() == 512  # 16 · λ

    def test_specialize_的_U_n(self, crs):
        sn = specialize(crs, 8)
        assert sn.U_n == pow(crs.g, sn.e_all, crs.N)
        assert sn.e_all == product_tree(crs.primegen.first(8))
        assert sn.n == 8

    def test_specialize_超容量报错(self, crs):
        with pytest.raises(ValueError, match="只准备了"):
            specialize(crs, 100)

    def test_参数非法时报错(self):
        with pytest.raises(ValueError):
            setup(lambda_bits=0, l=8, n=4)
        with pytest.raises(ValueError):
            setup(lambda_bits=32, l=0, n=4)
        with pytest.raises(ValueError):
            setup(lambda_bits=32, l=8, n=0)


# ---------------------------------------------------------------------------
# #20 commit
# ---------------------------------------------------------------------------

class TestCommit:
    def test_批处理与朴素路径一致(self, crs_n, values):
        a = commit(crs_n, values, use_batch=True)
        b = commit(crs_n, values, use_batch=False)
        assert a.C == b.C

    def test_承诺大小与长度无关(self, crs):
        """常量大小承诺：元素个数不影响 C 的长度。"""
        sizes = []
        for n in (8, 16):
            sn = specialize(crs, n)
            vals = [i + 1 for i in range(n)]
            sizes.append(commit(sn, vals).C.bit_length())
        assert all(s <= 256 for s in sizes), sizes

    def test_aux_就是原始数据(self, crs_n, values):
        assert commit(crs_n, values).aux == values

    def test_长度不符报错(self, crs_n):
        with pytest.raises(ValueError, match="长度"):
            commit(crs_n, [1, 2, 3])

    def test_可复现(self, crs_n, values):
        assert commit(crs_n, values).C == commit(crs_n, values).C

    def test_不同数据不同承诺(self, crs_n, values):
        other = list(values)
        other[0] += 1
        assert commit(crs_n, values).C != commit(crs_n, other).C


# ---------------------------------------------------------------------------
# #21 ~ #22 open / verify
# ---------------------------------------------------------------------------

class TestOpenVerify:
    def test_正确打开通过验证(self, crs_n, values, committed):
        pi = open_subvector(
            crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values
        )
        assert verify(
            crs_n, committed.C, I_SAMPLE, [values[i] for i in I_SAMPLE], pi
        ).ok

    def test_打开证明只有两个群元素(self, crs_n, values):
        pi = open_subvector(crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values)
        assert isinstance(pi.S_I, int) and isinstance(pi.Lambda_I, int)

    def test_打开下标集合大小不影响证明大小(self, crs_n, values):
        small = open_subvector(crs_n, [0], [values[0]], values)
        big = open_subvector(
            crs_n, list(range(crs_n.n)), list(values), values
        )
        assert type(small.S_I) is type(big.S_I)

    def test_值被改动则失败_且指出是_Lambda_环节(self, crs_n, values, committed):
        pi = open_subvector(
            crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values
        )
        lying = list(values[i] for i in I_SAMPLE)
        lying[0] += 1
        report = verify(crs_n, committed.C, I_SAMPLE, lying, pi)
        assert not report.ok
        assert report.code is VerifyCode.BAD_LAMBDA

    def test_承诺被换掉则失败(self, crs_n, values, committed):
        pi = open_subvector(
            crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values
        )
        other = list(values)
        other[0] += 1
        bad_c = commit(crs_n, other).C
        report = verify(
            crs_n, bad_c, I_SAMPLE, [values[i] for i in I_SAMPLE], pi
        )
        assert not report.ok
        assert report.code is VerifyCode.BAD_LAMBDA

    def test_伪造_S_I_则在第一步被拦下(self, crs_n, values, committed):
        pi = open_subvector(
            crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values
        )
        from svc import Opening

        forged = Opening(
            S_I=(pi.S_I * 2) % crs_n.N, Lambda_I=pi.Lambda_I, I=pi.I
        )
        report = verify(
            crs_n, committed.C, I_SAMPLE, [values[i] for i in I_SAMPLE], forged
        )
        assert not report.ok
        assert report.code is VerifyCode.BAD_S_I

    def test_形状检查(self, crs_n, values, committed):
        pi = open_subvector(
            crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values
        )
        # I 有重复下标
        r = verify(crs_n, committed.C, [1, 1, 4], [values[1], values[1], values[4]], pi)
        assert r.code is VerifyCode.BAD_SHAPE
        # 下标越界
        r = verify(crs_n, committed.C, [999], [1], pi)
        assert r.code is VerifyCode.BAD_SHAPE
        # 值个数不匹配
        r = verify(crs_n, committed.C, I_SAMPLE, [1, 2], pi)
        assert r.code is VerifyCode.BAD_SHAPE
        # 证明里的下标与传入的不一致
        r = verify(crs_n, committed.C, [0, 1, 2], [values[i] for i in (0, 1, 2)], pi)
        assert r.code is VerifyCode.BAD_SHAPE

    def test_迭代器下标不被误判(self, crs_n, values, committed):
        """``I`` 传迭代器也必须能通过（审计【8】）。

        形状检查会消费 ``I``：旧写法在检查之后才 ``list(I)``，拿到的已是空表，
        于是把合法的 ``iter([...])`` 误判成「I 里有重复下标」。
        """
        vals_I = [values[i] for i in I_SAMPLE]
        pi = open_subvector(crs_n, I_SAMPLE, vals_I, values)
        r = verify(crs_n, committed.C, iter(I_SAMPLE), vals_I, pi)
        assert r.ok, r.message

    def test_下标顺序不影响打开结果(self, crs_n, values):
        """I 会被规范化成升序元组，乱序传入应当得到同样的证明。"""
        a = open_subvector(crs_n, [9, 1, 4], [values[9], values[1], values[4]], values)
        b = open_subvector(crs_n, [1, 4, 9], [values[1], values[4], values[9]], values)
        assert a.S_I == b.S_I and a.Lambda_I == b.Lambda_I

    def test_open_声明值与_aux_不符时报错(self, crs_n, values):
        with pytest.raises(ValueError, match="不符"):
            open_subvector(crs_n, [1], [values[1] + 1], values)

    def test_空的打开集合(self, crs_n, values, committed):
        """I = ∅ 时 e_∅ = 1（空乘积），于是 S_∅ = g^{e_[n]} = U_n、Λ_∅ = C。"""
        pi = open_subvector(crs_n, [], [], values)
        assert pi.S_I == crs_n.U_n, "S_∅ = g^{e_[n]/e_∅} = g^{e_[n]} = U_n"
        assert pi.Lambda_I == committed.C % crs_n.N, (
            "Λ_∅ = (∏_j S_j^{v_j})^{1/e_∅} = C（e_∅ = 1）"
        )
        assert verify(crs_n, committed.C, [], [], pi).ok

    def test_VerifyReport_可当布尔用(self, crs_n, values, committed):
        pi = open_subvector(crs_n, I_SAMPLE, [values[i] for i in I_SAMPLE], values)
        assert bool(verify(crs_n, committed.C, I_SAMPLE, [values[i] for i in I_SAMPLE], pi))
