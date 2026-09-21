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

import pytest

from server.app import N_MAX_CAP, TUNE_LADDER, tune_for, op_tune


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
