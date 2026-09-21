"""§8.2 两段式更新的测试 —— ``PushUpdate`` / ``ApplyUpdate``。

与 ``test_updates.py``（走系统级封装 ``update_modify`` 等）的区别：
这里逐个考察**协议本身**，尤其那条此前没被兑现的性质 ——

    ``ApplyUpdate`` **不读改动后的内容**，只凭 ``δ``、``∆``、``Υ∆``
    和自己的份额就能跟上；

以及 ``Υ∆`` 一旦被动过手脚（篡改 / 重放），必须在应用之前被拦下。
"""

from __future__ import annotations

import pytest

from vds import VDSSession, apply_update, push_update
from vds.storage_node import UpdateDelta, UpdateWitness

BLOCK_BYTES = 4
N_MAX = 48
N_BLOCKS = 32


@pytest.fixture
def session():
    return VDSSession(
        n_max=N_MAX, l=BLOCK_BYTES * 8, lambda_bits=16,
        modulus_bits=256, seed=b"pytest-proto",
    )


@pytest.fixture
def deployed(session):
    """32 块文件分给 2 个节点：holder 拿前半，blind 拿后半。"""
    delta, crs_n, values, _ = session.commit_bytes(bytes(range(64)) * 2, BLOCK_BYTES)
    nodes = session.distribute(
        delta, values, [list(range(0, 16)), list(range(16, 32))]
    )
    return {
        "delta": delta, "crs_n": crs_n, "values": values,
        "holder": nodes[0], "blind": nodes[1], "session": session,
    }


def _witness_ok(w, session, U):
    return w.verify(session.crs.primegen, session.crs.N, U)


# ---------------------------------------------------------------------------
# Υ∆ 自身的校验
# ---------------------------------------------------------------------------

class TestWitnessVerify:
    def test_mod的见证通过(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        p = push_update(s, d, deployed["holder"], UpdateDelta("mod", [2, 5], (7, 9)))
        ok, why = _witness_ok(p.witness, s, d.U)
        assert ok and why == ""

    def test_add的见证是旧的U(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        p = push_update(s, d, deployed["holder"], UpdateDelta("add", [32, 33], (1, 2)))
        assert p.witness.S_K == d.U
        ok, _ = _witness_ok(p.witness, s, d.U)
        assert ok

    def test_del的见证是新摘要的U(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        # 末尾那截在 blind 手里，所以由它发起
        p = push_update(s, d, deployed["blind"], UpdateDelta("del", [30, 31], ()))
        assert p.witness.S_K == p.delta.U
        assert p.witness.pi_K.S_I == p.delta.U and p.witness.pi_K.Lambda_I == p.delta.C

    def test_S_K被改动则不通过(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        p = push_update(s, d, deployed["holder"], UpdateDelta("mod", [2], (7,)))
        bad = UpdateWitness("mod", p.witness.K, p.witness.S_K * 3 % s.crs.N, p.witness.F_K)
        ok, why = _witness_ok(bad, s, d.U)
        assert not ok and "Υ∆ 校验失败" in why

    def test_缺少S_K(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        w = UpdateWitness("mod", [2], None, (0,))
        ok, why = _witness_ok(w, s, d.U)
        assert not ok and "没有更新密钥" in why

    def test_空K(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        ok, why = _witness_ok(UpdateWitness("mod", (), 1, ()), s, d.U)
        assert not ok and "K 为空" in why

    def test_未知op(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        ok, why = _witness_ok(UpdateWitness("wat", [2], d.U, ()), s, d.U)
        assert not ok and "未知的 op" in why


# ---------------------------------------------------------------------------
# 无数据跟进：ApplyUpdate 不读改动后的内容
# ---------------------------------------------------------------------------

class TestBlindApply:
    @pytest.mark.parametrize(
        "op",
        [
            UpdateDelta("mod", [1, 4, 9], (0xAAAA, 0xBBBB, 0xCCCC)),
            UpdateDelta("add", [32, 33, 34], (11, 22, 33)),
        ],
        ids=["mod", "add"],
    )
    def test_blind节点算出的摘要与Push方一致(self, deployed, op):
        s, d = deployed["session"], deployed["delta"]
        pushed = push_update(s, d, deployed["holder"], op)
        out = apply_update(s, d, deployed["blind"], op, pushed.witness)

        assert out.ok
        assert out.delta.U == pushed.delta.U
        assert out.delta.C == pushed.delta.C
        assert out.delta.n == pushed.delta.n

    def test_del时另一侧也能跟进(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("del", [30, 31], ())
        pushed = push_update(s, d, deployed["blind"], op)      # 持有末尾的那一方发起
        out = apply_update(s, d, deployed["holder"], op, pushed.witness)
        assert out.ok
        assert out.delta.C == pushed.delta.C
        assert out.node.check_local_view()

    @pytest.mark.parametrize(
        "op",
        [
            UpdateDelta("mod", [1, 4], (0xAAAA, 0xBBBB)),
            UpdateDelta("add", [32, 33], (11, 22)),
        ],
        ids=["mod", "add"],
    )
    def test_blind节点更新后视图仍合法(self, deployed, op):
        s, d = deployed["session"], deployed["delta"]
        pushed = push_update(s, d, deployed["holder"], op)
        out = apply_update(s, d, deployed["blind"], op, pushed.witness)
        assert out.node.check_local_view()

    def test_mod_不影响持有K的节点的证明(self, deployed):
        """改的位置在 I 内时，Λ_I 完全不用动（它只含 I 外的值）。"""
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("mod", [1, 4], (0xAAAA, 0xBBBB))
        out = apply_update(s, d, deployed["holder"], op,
                           push_update(s, d, deployed["holder"], op).witness)
        assert out.ok
        assert out.node.st.Lambda_I == deployed["holder"].st.Lambda_I
        assert out.node.st.S_I == deployed["holder"].st.S_I
        # 但值确实换了
        assert out.node.view.value_of(1) == 0xAAAA

    def test_改的位置在blind手里时blind自己也算得对(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        # blind 持有 16..31，改 20 就在它手里
        op = UpdateDelta("mod", [20, 25], (0xDEAD, 0xBEEF))
        pushed = push_update(s, d, deployed["blind"], op)
        out = apply_update(s, d, deployed["blind"], op, pushed.witness)
        assert out.ok and out.delta.C == pushed.delta.C
        assert out.node.view.value_of(20) == 0xDEAD
        assert out.node.check_local_view()

    def test_add_后blind的值表不变(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("add", [32, 33], (11, 22))
        out = apply_update(s, d, deployed["blind"], op,
                           push_update(s, d, deployed["holder"], op).witness)
        assert out.node.I == deployed["blind"].I
        assert out.node.FI == deployed["blind"].FI

    def test_del后发起方丢掉被删的下标(self, session, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("del", [30, 31], ())
        pushed = push_update(s, d, deployed["blind"], op)
        out = apply_update(s, d, deployed["blind"], op, pushed.witness)
        assert 30 not in out.node.I and 31 not in out.node.I
        assert out.delta.n == d.n - 2


# ---------------------------------------------------------------------------
# 拒绝路径
# ---------------------------------------------------------------------------

class TestReject:
    def test_篡改见证则原样不动(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("mod", [2], (0x1111,))
        p = push_update(s, d, deployed["holder"], op)
        bad = UpdateWitness("mod", p.witness.K, p.witness.S_K * 3 % s.crs.N, p.witness.F_K)
        out = apply_update(s, d, deployed["blind"], op, bad)
        assert not out.ok
        assert out.delta is None and out.node is None

    def test_重放同一份见证会被拦住(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("mod", [2], (0x1111,))
        p = push_update(s, d, deployed["holder"], op)

        first = apply_update(s, d, deployed["holder"], op, p.witness)
        assert first.ok
        second = apply_update(s, first.delta, first.node, op, p.witness)
        assert not second.ok
        assert "本地视图不合法" in second.message

    def test_op不一致被拒(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        p = push_update(s, d, deployed["holder"], UpdateDelta("mod", [2], (1,)))
        out = apply_update(s, d, deployed["blind"], UpdateDelta("add", [32], (1,)), p.witness)
        assert not out.ok and "op 不一致" in out.message

    def test_K不一致被拒(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        p = push_update(s, d, deployed["holder"], UpdateDelta("mod", [2], (1,)))
        out = apply_update(s, d, deployed["blind"], UpdateDelta("mod", [3], (1,)), p.witness)
        assert not out.ok and "K 不一致" in out.message

    def test_旧值个数对不上被拒(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("mod", [2, 3], (1, 2))
        p = push_update(s, d, deployed["holder"], op)
        bad = UpdateWitness("mod", p.witness.K, p.witness.S_K, (0,))
        out = apply_update(s, d, deployed["blind"], op, bad)
        assert not out.ok and "旧值个数" in out.message

    def test_del缺少pi_K被拒(self, deployed):
        s, d = deployed["session"], deployed["delta"]
        op = UpdateDelta("del", [30, 31], ())
        p = push_update(s, d, deployed["blind"], op)
        bad = UpdateWitness("del", p.witness.K, p.witness.S_K, p.witness.F_K, None)
        out = apply_update(s, d, deployed["holder"], op, bad)
        assert not out.ok and "π_K" in out.message


# ---------------------------------------------------------------------------
# Push 侧的保护
# ---------------------------------------------------------------------------

class TestPushGuards:
    def test_超过会话上限(self, session):
        d, _, vals, _ = session.commit_bytes(bytes(range(64)) * 2, BLOCK_BYTES)
        nodes = session.distribute(d, vals, [list(range(0, 32))])
        # n = 32，再追加 17 个就超过 n_max = 48
        with pytest.raises(ValueError, match="超过会话上限"):
            push_update(
                session, d, nodes[0],
                UpdateDelta("add", list(range(32, 49)), (1,) * 17),
            )

    def test_刚好用满上限可以追加(self, session):
        d, _, vals, _ = session.commit_bytes(bytes(range(64)) * 2, BLOCK_BYTES)
        nodes = session.distribute(d, vals, [list(range(0, 32))])
        p = push_update(
            session, d, nodes[0],
            UpdateDelta("add", list(range(32, 48)), (1,) * 16),
        )
        assert p.delta.n == N_MAX

    def test_del只能删末尾(self, session, deployed):
        with pytest.raises(ValueError, match="末尾"):
            push_update(deployed["session"], deployed["delta"], deployed["holder"],
                        UpdateDelta("del", [10, 11], ()))

    def test_del要求发起方持有K(self, deployed):
        # 末尾 [30,31] 在 blind 手里；holder 拿不出来
        with pytest.raises(ValueError, match="发起删除的节点必须持有"):
            push_update(deployed["session"], deployed["delta"], deployed["holder"],
                        UpdateDelta("del", [30, 31], ()))

    def test_mod的K越界(self, session, deployed):
        with pytest.raises(ValueError, match="越界"):
            push_update(deployed["session"], deployed["delta"], deployed["holder"],
                        UpdateDelta("mod", [N_BLOCKS], (1,)))

    def test_mod的值个数必须匹配(self, deployed):
        with pytest.raises(ValueError, match="长度必须一致"):
            push_update(deployed["session"], deployed["delta"], deployed["holder"],
                        UpdateDelta("mod", [1, 2], (1,)))

    def test_未知op(self, deployed):
        with pytest.raises(ValueError, match="未知的 op"):
            push_update(deployed["session"], deployed["delta"], deployed["holder"],
                        UpdateDelta("nope", [1], (1,)))
