"""文件大小 → 参数自适应（``/api/tune``、``server.app.tune_for``）的测试。

这一层要钉死的性质只有三条，但每条都必须成立：

1. **``n_max`` 永远等于真实块数** —— 即 ``ceil(nbytes / block_bytes)``。
   用户明确要求过：n max 只是素数表容量，实测对耗时没有影响，
   所以取「正好够用的最小值」，而不是给一个用不上的大容量。
2. **切块不丢数据** —— ``(n_max - 1) * block_bytes < nbytes <= n_max * block_bytes``。
   块数少算一块会让最后的尾块被截断，这是会静默丢数据的错误。
3. **返回的块大小必须是候选表里的一档** —— 前端输入框的 ``max`` 是 64，
   后端选出的档位不能越界，否则前端会拿到一个自己填不回去的值。
"""

from __future__ import annotations

import math

import pytest

from server.app import (
    BLOCK_BYTES_MAX,
    N_MAX_CAP,
    TUNE_LADDER,
    _PER_BYTE_MS,
    _per_byte_for,
    op_tune,
    tune_for,
)


#: 覆盖极小 / 常规 / 较大 / 超大四类规模
SIZES = [
    1, 2, 7, 15, 16, 17, 63, 64, 65,
    100, 511, 512, 4096, 17 * 1000,
    100_000, 1 << 20,
]


class TestTuneFor:

    @pytest.mark.parametrize("nbytes", SIZES)
    def test_n_max_正好等于块数(self, nbytes):
        r = tune_for(nbytes)
        expected = (nbytes + r["block_bytes"] - 1) // r["block_bytes"]
        assert r["n"] == expected
        assert r["n_max"] == expected, "n max 必须等于真实块数（用户要求的「最小够用」）"

    @pytest.mark.parametrize("nbytes", SIZES)
    def test_切块不丢数据(self, nbytes):
        r = tune_for(nbytes)
        bb, n = r["block_bytes"], r["n"]
        assert n * bb >= nbytes, "块数不足会把尾块截断 —— 静默丢数据"
        assert (n - 1) * bb < nbytes, "块数多算一块会凭空多出空块"

    @pytest.mark.parametrize("nbytes", SIZES)
    def test_块大小在候选表内(self, nbytes):
        r = tune_for(nbytes)
        assert r["block_bytes"] in TUNE_LADDER
        assert r["block_bytes"] <= 64, "前端输入框 max=64，越界就填不回去"

    @pytest.mark.parametrize("nbytes", SIZES)
    def test_返回结构完整(self, nbytes):
        r = tune_for(nbytes)
        for key in ("ok", "nbytes", "nodes", "block_bytes", "n_max", "n",
                    "est_ms", "feasible", "scanned", "reason"):
            assert key in r, f"缺字段 {key}"
        assert r["ok"] is True
        assert r["nbytes"] == nbytes
        assert r["est_ms"] > 0
        assert isinstance(r["reason"], str) and r["reason"]

    @pytest.mark.parametrize("nbytes", [4096, 100_000, 1 << 20])
    def test_选中的是可用候选里估算耗时最低的(self, nbytes):
        """常规规模下，选出的档位应当就是「预计最快」的那一档。"""
        r = tune_for(nbytes)
        pool = [s for s in r["scanned"] if s["feasible"]]
        assert pool, "常规规模下应当存在可行候选"
        best_est = min(s["est_ms"] for s in pool)
        assert r["est_ms"] == pytest.approx(best_est, rel=1e-9)

    def test_极小文件自动放宽可行性(self):
        """块数凑不满台数时，退化到「块数尽量多」而不是报错。

        可行性的判据是 ``n >= min(nodes, nbytes)``：8 字节、4 台时，
        最小的候选块 4 字节也只能切出 2 块（< 4 台），所有候选都不可行 ——
        此时应当挑块数最多的那一档，并如实标记 ``feasible=False``。
        """
        r = tune_for(8, nodes=4)
        assert r["ok"] is True
        assert r["block_bytes"] == 4     # 块数最多的一档
        assert r["n"] == 2
        assert r["feasible"] is False    # 如实告知：块数 < 台数，分发会截断

    def test_一字节文件不算退化(self):
        """1 字节：只有 1 台服务器能拿到东西，就没有「空服务器」问题。"""
        r = tune_for(1, nodes=4)
        assert r["ok"] is True
        assert r["n"] == 1
        # min(nodes, nbytes) = min(4, 1) = 1，块数 1 >= 1 → 可行
        assert r["feasible"] is True

    def test_常规文件可行(self):
        r = tune_for(65536, nodes=4)
        assert r["feasible"] is True
        assert r["n"] >= 4

    def test_超过上限时如实降级(self):
        """大到连最大块都放不下 n_max 上限：取最大块并标记不可行。"""
        nbytes = N_MAX_CAP * TUNE_LADDER[-1] + 1
        r = tune_for(nbytes)
        assert r["block_bytes"] == TUNE_LADDER[-1]
        assert r["feasible"] is False
        assert "上限" in r["reason"]

    def test_没有可用块大小时不给做不到的建议(self):
        """连最大块都救不了 → 不能给「把每块调到 N 字节」，那样用户照做仍然跑不起来。

        这个分支里 ceil(nbytes / N_MAX_CAP) 必然 > 64，所以只能置 None，
        并在 reason 里改说「换小一点的文件」。
        """
        nbytes = N_MAX_CAP * BLOCK_BYTES_MAX + 1
        r = tune_for(nbytes)
        assert r["over_cap"] is True
        assert r["feasible"] is False
        assert r["min_block_bytes"] is None
        assert "小一点的文件" in r["reason"], "要给一条真能执行的出路"

    def test_刚好放得下时不给降级(self):
        """边界另一侧：正好等于上限容量，应当能正常给出方案。"""
        r = tune_for(N_MAX_CAP * BLOCK_BYTES_MAX)
        assert r["over_cap"] is False
        assert r["n"] == r["n_max"] == N_MAX_CAP

    def test_n_max_永不超硬上限(self):
        for nbytes in (1, 4096, 1 << 20, N_MAX_CAP * 64 + 5):
            assert tune_for(nbytes)["n_max"] <= N_MAX_CAP

    def test_台数越多分发代价越高(self):
        """distribute 代价与台数 positive 相关，估算值应当随 k 上升。"""
        k4 = tune_for(65536, nodes=4)
        k16 = tune_for(65536, nodes=16)
        assert k16["est_ms"] > k4["est_ms"]

    def test_模数越大越慢(self):
        small = tune_for(65536, modulus_bits=512)
        big = tune_for(65536, modulus_bits=2048)
        assert big["est_ms"] > small["est_ms"] * 5


class TestOpTune:

    def test_非正字节数报错(self):
        for bad in (0, -1):
            with pytest.raises(ValueError):
                op_tune({"nbytes": bad})

    def test_缺省参数可用(self):
        r = op_tune({"nbytes": 4096})
        assert r["ok"] is True
        assert r["nodes"] == 4   # 默认 4 台

    def test_透传参数(self):
        r = op_tune({"nbytes": 65536, "nodes": 8, "modulus_bits": 1024})
        assert r["nodes"] == 8
        assert r["n_max"] == r["n"]

    def test_透传块大小(self):
        """前端「按每块字节数算块数」按钮走的就是这条：把用户填的块大小透传进来。"""
        r = op_tune({"nbytes": 20000, "block_bytes": 20})
        assert r["requested_block_bytes"] == 20
        assert r["block_bytes"] == 20, "不能把用户填的块大小换成「最快的那档」"
        assert r["n_max"] == math.ceil(20000 / 20)

    def test_块大小给空串等于没给(self):
        """前端输入框可能被清空 —— 空串应当走自动挑，而不是报错。"""
        assert op_tune({"nbytes": 4096, "block_bytes": ""}) == op_tune({"nbytes": 4096})
        assert op_tune({"nbytes": 4096, "block_bytes": None}) == op_tune({"nbytes": 4096})

    def test_非法块大小报错(self):
        for bad in (0, -3, BLOCK_BYTES_MAX + 1):
            with pytest.raises(ValueError):
                op_tune({"nbytes": 4096, "block_bytes": bad})


class Test指定块大小:
    """模式 A：尊重调用方填的每块字节数，只按它算块数。

    这是「不要替我挑块大小，我自己填，你只管把块数算对」这条需求的核心 ——
    无论用户填的是标定档还是任意值，块大小都必须原样保留。
    """

    @pytest.mark.parametrize("nbytes", SIZES)
    @pytest.mark.parametrize("bb", [1, 4, 7, 16, 20, 32, 64])
    def test_块大小原样保留(self, nbytes, bb):
        r = tune_for(nbytes, block_bytes=bb)
        assert r["block_bytes"] == bb, "用户填的块大小必须原样保留"
        assert r["requested_block_bytes"] == bb

    @pytest.mark.parametrize("nbytes", SIZES)
    @pytest.mark.parametrize("bb", [1, 4, 7, 16, 20, 32, 64])
    def test_n_max_就是按该块大小切出的块数(self, nbytes, bb):
        r = tune_for(nbytes, block_bytes=bb)
        expect = math.ceil(nbytes / bb)
        assert r["n"] == expect
        assert r["n_max"] == min(expect, N_MAX_CAP)

    @pytest.mark.parametrize("nbytes", SIZES)
    @pytest.mark.parametrize("bb", [1, 4, 7, 16, 20, 32, 64])
    def test_切块不丢数据(self, nbytes, bb):
        r = tune_for(nbytes, block_bytes=bb)
        assert r["n"] * bb >= nbytes, "块数不足会把尾块截断 —— 静默丢数据"
        assert (r["n"] - 1) * bb < nbytes, "块数多算一块会凭空多出空块"

    def test_大文件配小块会如实报超上限(self):
        """块太小 → 块数突破上限 → 建不了会话。必须报出来，并给出最小的可用块大小。"""
        nbytes, bb = 2_000_000, 16
        r = tune_for(nbytes, block_bytes=bb)
        assert r["over_cap"] is True
        assert r["feasible"] is False
        assert r["n"] == math.ceil(nbytes / bb) > N_MAX_CAP
        assert r["n_max"] == N_MAX_CAP, "给不出超过上限的容量，只能给到上限"
        assert r["min_block_bytes"] == math.ceil(nbytes / N_MAX_CAP)
        assert str(r["min_block_bytes"]) in r["reason"], "提示里要有可操作的数字"

    @pytest.mark.parametrize("nbytes", [1, 64, 4096, 65536])
    def test_没超上限就不报超上限(self, nbytes):
        r = tune_for(nbytes, block_bytes=64)
        assert r["over_cap"] is False
        assert r["min_block_bytes"] is None

    def test_更快的档只作提示不覆盖用户选择(self):
        r = tune_for(20000, block_bytes=8)
        assert r["block_bytes"] == 8, "即使用户选的不是最快档，也不能替他改"
        assert r["suggestion"] is not None
        assert r["suggestion"]["est_ms"] < r["est_ms"]
        assert r["suggestion"]["block_bytes"] != 8
        assert r["suggestion"]["gain_pct"] > 0

    def test_已经是最快档时不给提示(self):
        fastest = tune_for(20000)["block_bytes"]   # 先问自动模式挑的是哪一档
        r = tune_for(20000, block_bytes=fastest)
        assert r["suggestion"] is None

    def test_非法块大小报错(self):
        for bad in (0, -1, BLOCK_BYTES_MAX + 1, 1000):
            with pytest.raises(ValueError):
                tune_for(4096, block_bytes=bad)


class Test每字节代价插值:
    """标定表只有 8 档，但用户能填 1~64 任意值，所以要能给任意 bb 估耗时。"""

    @pytest.mark.parametrize("bb", sorted(_PER_BYTE_MS))
    def test_标定档不被插值扰动(self, bb):
        """标定过的档必须原样返回 —— 插值绝不能动到实测值本身。"""
        assert _per_byte_for(bb) == _PER_BYTE_MS[bb]

    @pytest.mark.parametrize("bb", range(5, 64))
    def test_插值落在相邻标定档之间(self, bb):
        """log-log 插值的硬性质：两个分量都落在左右两档之间，不会外冲出界。"""
        keys = sorted(_PER_BYTE_MS)
        lo = max(k for k in keys if k <= bb)
        hi = min(k for k in keys if k >= bb)
        c, d = _per_byte_for(bb)
        c0, d0 = _PER_BYTE_MS[lo]
        c1, d1 = _PER_BYTE_MS[hi]
        assert min(c0, c1) - 1e-12 <= c <= max(c0, c1) + 1e-12
        assert min(d0, d1) - 1e-12 <= d <= max(d0, d1) + 1e-12

    def test_超出标定范围取最近的档(self):
        for bb in (1, 2, 3):
            assert _per_byte_for(bb) == _PER_BYTE_MS[4]
        assert _per_byte_for(64) == _PER_BYTE_MS[64]
        assert _per_byte_for(200) == _PER_BYTE_MS[64]

    def test_相邻块大小的估值不会突然跳变(self):
        """1~48 之间应当平滑。

        48→64 有一次**真实**跳变（素数从 385 位涨到 513 位，实测每字节代价翻倍），
        那是标定表里的真实数据、不是插值缺陷，所以这段被排除在外。
        """
        prev = None
        for bb in range(4, 49):
            est = tune_for(20000, block_bytes=bb)["est_ms"]
            if prev is not None:
                ratio = max(est, prev) / min(est, prev)
                assert ratio < 1.15, f"bb={bb} 相比上一档跳变 {ratio:.2f}×"
            prev = est
