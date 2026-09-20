"""论文 §8.1 的 ``VDS1`` 测试。

分五块：

1. **Bootstrap / VC.Com' / VC.Ver'** —— 摘要与本地视图的定义；
2. **分发、检索、聚合** —— ``Retrieve`` / ``VerRetrieve`` / ``AggregateCertificates``；
3. **CreateFrom / GetCreate** —— 从一个已存文件派生子文件，
   这是 ``VDS1`` 相比 §8.2 多出来的能力；
4. **三种更新** —— ``mod`` / ``add`` / ``del`` 的 Push + Apply，
   其中 ``mod`` 与 ``del`` 的本地状态更新分 ``I ∩ K`` 的三种情形，
   测试对三种都单独造了节点；
5. **攻击面** —— 伪造 ``Υ_∆``、陈旧摘要、重放。
"""

from __future__ import annotations

import pytest

from svc import DeterministicRNG
from vds.vds1 import (
    ClientNode1,
    CreateWitness,
    LocalView1,
    PushedUpdate1,
    StorageNode1,
    UpdateOp1,
    VDS1Session,
    com_prime,
    disagg_prime,
    is_prefix,
    poksubv_prime_prove,
    poksubv_prime_verify,
    ver_prime,
)

MODULUS_BITS = 256
LAMBDA = 16


# ---------------------------------------------------------------------------
# 工具
# ---------------------------------------------------------------------------

def make_node(session, base, I, node_id="node"):
    """从 ``base``（持有全集）拆出一个只持有 ``I`` 的节点。"""
    keep = list(I)
    drop = [i for i in base.I if i not in set(keep)]
    node = base.rmv_storage(drop) if drop else base
    return StorageNode1(node_id, session, node.view)


def node_of(session, pushed_or_result, node_id="node"):
    """把一个 ``PushedUpdate1`` / ``AppliedUpdate1`` 的结果变成节点。"""
    return StorageNode1(
        node_id, session,
        LocalView1(pushed_or_result.delta, pushed_or_result.st,
                   pushed_or_result.J, pushed_or_result.F_J),
    )


def apply_and_wrap(session, node, op, pushed, node_id=None):
    """跑 ``ApplyUpdate`` 并把结果包成新节点；失败时返回 ``(None, res)``。"""
    res = node.apply_update(op, pushed)
    if not res.ok:
        return None, res
    return node_of(session, res, node_id or node.node_id), res


# ---------------------------------------------------------------------------
# 夹具：一条 mod → add → del 的更新链
# ---------------------------------------------------------------------------

N0 = 12


@pytest.fixture(scope="module")
def session():
    return VDS1Session(n_max=24, lambda_bits=LAMBDA, modulus_bits=MODULUS_BITS,
                       seed=b"pytest-vds1")


@pytest.fixture(scope="module")
def v0():
    rng = DeterministicRNG(b"pytest-vds1-vals")
    return tuple(rng.randbelow(2) for _ in range(N0))


@pytest.fixture(scope="module")
def R0(session, v0):
    """初始的根节点：持有 12 个块，摘要为 :math:`\\delta_0` 之后的第一个真实摘要。"""
    delta, st = session.commit(v0)
    return StorageNode1("root", session,
                        LocalView1(delta, st, list(range(N0)), list(v0)))


@pytest.fixture(scope="module")
def V1(v0):
    """``mod`` 之后的取值。"""
    vals = list(v0)
    vals[3] ^= 1
    vals[4] ^= 1
    return tuple(vals)


@pytest.fixture(scope="module")
def OP_MOD(v0):
    return UpdateOp1("mod", [3, 4], [v0[3] ^ 1, v0[4] ^ 1])


@pytest.fixture(scope="module")
def P1(R0, OP_MOD):
    return R0.push_update(OP_MOD)


@pytest.fixture(scope="module")
def R1(session, P1):
    return node_of(session, P1, "root")


@pytest.fixture(scope="module")
def V2(V1):
    return V1 + (1, 0)


@pytest.fixture(scope="module")
def OP_ADD():
    return UpdateOp1("add", [12, 13], [1, 0])


@pytest.fixture(scope="module")
def P2(R1, OP_ADD):
    return R1.push_update(OP_ADD)


@pytest.fixture(scope="module")
def R2(session, P2):
    return node_of(session, P2, "root")


@pytest.fixture(scope="module")
def OP_DEL():
    return UpdateOp1("del", [12, 13])


@pytest.fixture(scope="module")
def P3(R2, OP_DEL):
    return R2.push_update(OP_DEL)


@pytest.fixture(scope="module")
def R3(session, P3):
    return node_of(session, P3, "root")


# ---------------------------------------------------------------------------
# 1. Bootstrap 与摘要算法
# ---------------------------------------------------------------------------

class TestBootstrap:
    def test_初始摘要是_两个生成元_与长度_0(self, session):
        delta0, st0 = session.bootstrap()
        assert (delta0.A, delta0.B, delta0.n) == (
            session.crs.g0, session.crs.g1, 0
        )

    def test_空文件的摘要与_Com_撇_一致(self, session):
        delta0, _ = session.bootstrap()
        assert com_prime(session.crs, []) == delta0

    def test_空文件的本地状态有效(self, session):
        delta0, st0 = session.bootstrap()
        assert ver_prime(session.crs, delta0, [], [], st0)

    def test_根打开就是_st0_同形(self, session, v0, R0):
        # 补集为空时 Γ = g0、Δ = g1
        assert R0.st.Gamma[0] == session.crs.g0
        assert R0.st.Delta[0] == session.crs.g1


class TestComPrime:
    def test_承诺的两个分量对应集合划分(self, session, v0):
        delta = com_prime(session.crs, v0)
        assert delta.n == N0
        assert delta == session.commit(v0)[0]

    def test_相同向量承诺相同(self, session, v0):
        assert com_prime(session.crs, v0) == com_prime(session.crs, v0)

    def test_改一个比特摘要就变(self, session, v0):
        bad = list(v0)
        bad[0] ^= 1
        assert com_prime(session.crs, bad) != com_prime(session.crs, v0)

    def test_值越界报错(self, session):
        with pytest.raises(ValueError):
            com_prime(session.crs, [2])

    def test_ver_prime_拒绝篡改的本地视图(self, session, v0, R0):
        assert ver_prime(session.crs, R0.delta, list(R0.I), list(R0.FI), R0.st)
        bad = list(v0)
        bad[2] ^= 1
        assert not ver_prime(session.crs, R0.delta, list(R0.I), bad, R0.st)

    def test_ver_prime_空_vals_与空下标都通过(self, session):
        delta0, st0 = session.bootstrap()
        assert ver_prime(session.crs, delta0, [], (), st0)
        assert not ver_prime(session.crs, delta0, [0], (), st0)

    def test_ver_prime_长度不匹配被拒(self, session, v0, R0):
        assert not ver_prime(session.crs, R0.delta, list(R0.I), list(v0[:-1]),
                             R0.st)

    def test_ver_prime_越界下标被拒(self, session, v0, R0):
        assert not ver_prime(session.crs, R0.delta, [N0], [0], R0.st)

    def test_is_prefix(self):
        assert is_prefix([])
        assert is_prefix([0, 1, 2])
        assert not is_prefix([1, 2])
        assert not is_prefix([0, 1, 3])


class TestLocalView:
    def test_下标与值长度必须一致(self, session, R0):
        with pytest.raises(ValueError):
            LocalView1(R0.delta, R0.st, [0, 1], [0])

    def test_状态下标与视图下标必须一致(self, session, R0):
        with pytest.raises(ValueError):
            LocalView1(R0.delta, R0.st, [0, 1], [0, 1])

    def test_value_of_缺失下标抛错(self, session, R0):
        node = make_node(session, R0, [4, 5], "part")
        with pytest.raises(KeyError):
            node.view.value_of(0)
        assert node.view.value_of(4) == node.FI[0]

    def test_node_of_重建的视图有效(self, session, P1):
        assert node_of(session, P1, "x").check_local_view()


# ---------------------------------------------------------------------------
# 2. 检索、验证、聚合
# ---------------------------------------------------------------------------

class TestRetrieve:
    @pytest.mark.parametrize("size", [1, 3, 6, 12])
    def test_任意子集都能被客户端独立验证(self, session, R0, size):
        client = ClientNode1("c", session, R0.delta)
        Q = list(range(size))
        F_Q, pi_Q = R0.retrieve(Q)
        assert client.ver_retrieve(Q, F_Q, pi_Q)
        assert F_Q == tuple(R0.FI[i] for i in Q)

    def test_篡改一个值被拒(self, session, R0):
        client = ClientNode1("c", session, R0.delta)
        Q = [0, 1, 2]
        F_Q, pi_Q = R0.retrieve(Q)
        bad = list(F_Q)
        bad[1] ^= 1
        assert not client.ver_retrieve(Q, bad, pi_Q)

    def test_篡改证据被拒(self, session, R0):
        from svc.yinyan import Opening1

        client = ClientNode1("c", session, R0.delta)
        Q = [0, 1, 2]
        F_Q, pi_Q = R0.retrieve(Q)
        tampered = Opening1(
            (pi_Q.Gamma[0] * 3 % session.crs.N,), pi_Q.Delta, tuple(Q)
        )
        assert not client.ver_retrieve(Q, F_Q, tampered)

    def test_检索不在本地的下标报错(self, session, R0):
        node = make_node(session, R0, [0, 1, 2])
        with pytest.raises(ValueError):
            node.retrieve([5])

    def test_拆出来的子节点能回答自己的那段(self, session, R0):
        node = make_node(session, R0, [4, 5, 6])
        client = ClientNode1("c", session, node.delta)
        F_Q, pi_Q = node.retrieve([5, 6])
        assert client.ver_retrieve([5, 6], F_Q, pi_Q)

    def test_has(self, session, R0):
        node = make_node(session, R0, [4, 5])
        assert node.has([4])
        assert not node.has([4, 7])


class TestAggregate:
    def test_三份合并成一份(self, session, R0, v0):
        parts, idx = [], [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]]
        for Q in idx:
            F, pi = R0.retrieve(Q)
            parts.append((Q, F, pi))
        client = ClientNode1("c", session, R0.delta)
        merged = client.aggregate_certificates(parts)
        assert merged.I == tuple(range(N0))
        assert client.ver_retrieve(list(range(N0)), v0, merged)

    def test_两份版本(self, session, R0, v0):
        client = ClientNode1("c", session, R0.delta)
        Fa, pa = R0.retrieve([0, 1, 2])
        Fb, pb = R0.retrieve([3, 4, 5])
        merged = client.aggregate_two([0, 1, 2], Fa, pa, [3, 4, 5], Fb, pb)
        assert client.ver_retrieve(list(range(6)), v0[:6], merged)

    def test_合并不要求节点持有并集(self, session, R0, v0):
        """两份证据来自不同节点，客户端照样能合成一个。"""
        left = make_node(session, R0, list(range(0, 6)), "L")
        right = make_node(session, R0, list(range(6, 12)), "R")
        Fa, pa = left.retrieve([0, 1, 2])
        Fb, pb = right.retrieve([9, 10])
        client = ClientNode1("c", session, R0.delta)
        merged = client.aggregate_two([0, 1, 2], Fa, pa, [9, 10], Fb, pb)
        assert client.ver_retrieve([0, 1, 2, 9, 10],
                                   [v0[i] for i in (0, 1, 2, 9, 10)], merged)


class TestAddRmvStorage:
    def test_两份不相交的存储合并(self, session, R0, v0):
        left = make_node(session, R0, [0, 1, 2, 3], "L")
        right = make_node(session, R0, [4, 5, 6, 7], "R")
        both = left.add_storage(right)
        assert both.I == (0, 1, 2, 3, 4, 5, 6, 7)
        assert both.check_local_view()
        client = ClientNode1("c", session, both.delta)
        F_Q, pi_Q = both.retrieve([0, 3, 7])
        assert client.ver_retrieve([0, 3, 7], F_Q, pi_Q)

    def test_空节点合并等于原样接收(self, session, R0):
        empty = StorageNode1(
            "empty", session, LocalView1(R0.delta, R0.st, (), ())
        )
        merged = empty.add_storage(make_node(session, R0, [0, 1], "A"))
        assert merged.I == (0, 1)
        assert merged.check_local_view()

    def test_有重叠时报错(self, session, R0):
        left = make_node(session, R0, [0, 1, 2], "L")
        right = make_node(session, R0, [2, 3, 4], "R")
        with pytest.raises(ValueError):
            left.add_storage(right)

    def test_摘要不同时报错(self, session, R0, V1, OP_MOD):
        other = node_of(session, R0.push_update(OP_MOD), "other")
        with pytest.raises(ValueError):
            make_node(session, R0, [0, 1], "L").add_storage(
                make_node(session, other, [2, 3], "R")
            )

    def test_删掉一部分后仍然有效(self, session, R0):
        node = R0.rmv_storage([0, 1, 2, 3])
        assert node.I == (4, 5, 6, 7, 8, 9, 10, 11)
        assert node.check_local_view()

    def test_删空报错(self, session, R0):
        with pytest.raises(ValueError):
            R0.rmv_storage(list(range(N0)))

    def test_删不持有下标报错(self, session, R0):
        node = make_node(session, R0, [0, 1])
        with pytest.raises(ValueError):
            node.rmv_storage([5])


# ---------------------------------------------------------------------------
# 3. CreateFrom / GetCreate
# ---------------------------------------------------------------------------

class TestCreateFrom:
    @pytest.mark.parametrize("m", [1, 2, 5, 8, 12])
    def test_派生子节点的摘要与本地视图都正确(self, session, R0, v0, m):
        J = list(range(m))
        derived, upsilon = R0.create_from(J)
        assert upsilon.delta == com_prime(session.crs, v0[:m])
        assert upsilon.delta.n == m
        assert derived.I == tuple(J)
        assert derived.delta == upsilon.delta
        assert derived.check_local_view()

    def test_客户端接受派生证明并拿到新摘要(self, session, R0, v0):
        client = ClientNode1("c", session, R0.delta)
        derived, upsilon = R0.create_from(list(range(5)))
        ok, delta_p = client.get_create(list(range(5)), upsilon)
        assert ok
        assert delta_p == com_prime(session.crs, v0[:5])

    def test_子文件可以被独立检索验证(self, session, R0, v0):
        derived, upsilon = R0.create_from(list(range(5)))
        sub_client = ClientNode1("sub", session, upsilon.delta)
        F_Q, pi_Q = derived.retrieve([0, 3, 4])
        assert sub_client.ver_retrieve([0, 3, 4], F_Q, pi_Q)
        assert F_Q == (v0[0], v0[3], v0[4])

    def test_派生证明是常数大小(self, session, R0):
        _, upsilon = R0.create_from(list(range(8)))
        # 一个群元素级别的消息：Γ、Δ、z 两个、Q 五个、r 两个
        assert hasattr(upsilon.proof, "QC")
        assert isinstance(upsilon.proof.ra, int)

    def test_J_不是前缀时报错(self, session, R0):
        with pytest.raises(ValueError):
            R0.create_from([1, 2, 3])

    def test_J_不是子集时报错(self, session, R0):
        with pytest.raises(ValueError):
            R0.create_from(list(range(N0, N0 + 2)))

    def test_空_J_报错(self, session, R0):
        with pytest.raises(ValueError):
            R0.create_from([])

    def test_客户端拒绝非前缀_J(self, session, R0):
        _, upsilon = R0.create_from(list(range(5)))
        client = ClientNode1("c", session, R0.delta)
        assert client.get_create([1, 2, 3], upsilon) == (False, None)

    def test_客户端拒绝长度不符的_J(self, session, R0):
        _, upsilon = R0.create_from(list(range(5)))
        client = ClientNode1("c", session, R0.delta)
        ok, delta_p = client.get_create(list(range(6)), upsilon)
        assert not ok and delta_p is None

    def test_客户端拒绝伪造的新摘要(self, session, R0, v0):
        _, upsilon = R0.create_from(list(range(5)))
        forged = CreateWitness(
            delta=com_prime(session.crs, v0[1:6]), proof=upsilon.proof
        )
        client = ClientNode1("c", session, R0.delta)
        ok, delta_p = client.get_create(list(range(5)), forged)
        assert not ok and delta_p is None

    def test_客户端拒绝替换了证据的派生(self, session, R0, v0):
        _, upsilon = R0.create_from(list(range(5)))
        other, other_upsilon = R0.create_from(list(range(6)))
        swapped = CreateWitness(delta=other_upsilon.delta, proof=upsilon.proof)
        client = ClientNode1("c", session, R0.delta)
        assert client.get_create(list(range(6)), swapped) == (False, None)

    def test_客户端拒绝来自别的摘要的派生(self, session, R0, R1):
        _, upsilon = R0.create_from(list(range(5)))
        client_other = ClientNode1("c", session, R1.delta)
        ok, _ = client_other.get_create(list(range(5)), upsilon)
        assert not ok

    def test_从子节点继续派生(self, session, R0, v0):
        """派生出 [0, 8) 之后，再从它派生出 [0, 3)。"""
        mid, ups1 = R0.create_from(list(range(8)))
        client = ClientNode1("c", session, R0.delta)
        assert client.get_create(list(range(8)), ups1)[0]
        leaf, ups2 = mid.create_from(list(range(3)))
        assert ups2.delta == com_prime(session.crs, v0[:3])
        mid_client = ClientNode1("m", session, ups1.delta)
        ok, _ = mid_client.get_create(list(range(3)), ups2)
        assert ok
        assert leaf.check_local_view()

    def test_常量时间的直接验证_不依赖_CreateFrom(self, session, R0):
        """``PoKSubV'`` 单独调用的接口也可用。"""
        J = list(range(4))
        delta_p = com_prime(session.crs, R0.FI[:4])
        pi_J = disagg_prime(session.crs, list(R0.I), list(R0.FI), R0.st, J)
        proof = poksubv_prime_prove(session.crs, R0.delta, delta_p, J,
                                    R0.FI[:4], pi_J)
        assert poksubv_prime_verify(session.crs, R0.delta, delta_p, J, proof)
        assert not poksubv_prime_verify(
            session.crs, R0.delta, delta_p, [1, 2, 3, 4], proof
        )


# ---------------------------------------------------------------------------
# 4. 更新
# ---------------------------------------------------------------------------

class TestModPush:
    def test_新摘要等于重新提交(self, session, P1, V1):
        assert P1.delta == com_prime(session.crs, V1)

    def test_长度不变(self, P1):
        assert P1.delta.n == N0

    def test_发布者状态不变(self, session, R0, P1):
        assert (P1.st.Gamma[0], P1.st.Delta[0]) == (
            R0.st.Gamma[0], R0.st.Delta[0]
        )

    def test_携带旧值与旧证据(self, session, R0, P1, v0):
        assert P1.F_K == (v0[3], v0[4])
        assert ver_prime(session.crs, R0.delta, [3, 4], list(P1.F_K), P1.pi_K)

    def test_发布者不持有_K_时报错(self, session, R0, OP_MOD):
        node = make_node(session, R0, [0, 1, 2])
        with pytest.raises(ValueError):
            node.push_update(OP_MOD)


class TestModApply:
    @pytest.fixture(scope="class")
    def cases(self, session, R0):
        """``I ∩ K`` 的三种情形各造一个节点。"""
        return {
            "I⊇K": make_node(session, R0, [2, 3, 4, 5], "over"),
            "I∩K=∅": make_node(session, R0, [6, 7, 8], "disj"),
            "I∩K=L": make_node(session, R0, [4, 5, 6], "part"),
        }

    def test_客户端接受并算出同一个新摘要(self, session, R0, OP_MOD, P1, V1):
        client = ClientNode1("c", session, R0.delta)
        ok, delta_p = client.apply_update(OP_MOD, P1)
        assert ok
        assert delta_p == P1.delta == com_prime(session.crs, V1)

    def test_三种情形的本地视图都更新正确(self, session, cases, OP_MOD, P1):
        for name, node in cases.items():
            new, res = apply_and_wrap(session, node, OP_MOD, P1, name)
            assert res.ok, name
            assert new.check_local_view(), name

    def test_三种情形的新取值都对(self, session, cases, OP_MOD, P1, V1):
        for name, node in cases.items():
            new, res = apply_and_wrap(session, node, OP_MOD, P1, name)
            assert list(new.FI) == [V1[i] for i in new.I], name

    def test_与_K_不相交的节点索引集合不变(self, session, cases, OP_MOD, P1):
        old = cases["I∩K=∅"]
        new, _ = apply_and_wrap(session, old, OP_MOD, P1)
        assert new.I == old.I
        assert new.FI == old.FI

    def test_与_K_完全重合的节点状态不变(self, session, cases, OP_MOD, P1, V1):
        old = cases["I⊇K"]
        new, _ = apply_and_wrap(session, old, OP_MOD, P1)
        assert new.I == old.I                    # 索引集合不变
        assert new.st.Gamma == old.st.Gamma      # 状态不变
        assert new.FI == (V1[2], V1[3], V1[4], V1[5])   # 值必须跟着变

    def test_部分重合的节点只更新重叠部分的值(self, session, cases,
                                              OP_MOD, P1, V1):
        old = cases["I∩K=L"]
        new, _ = apply_and_wrap(session, old, OP_MOD, P1)
        assert new.I == (4, 5, 6)
        assert new.FI == (V1[4], V1[5], V1[6])

    def test_伪造旧值被拒(self, session, cases, OP_MOD, P1):
        # 翻转一位就会改变零集合，从而改变 PartndPrimeProd 的两个分量。
        # 反过来，只有「零集合相同」的假值才不会破坏 Ver' ——
        # 所以伪造必须选这种改法（拿 mod 的新值冒充旧值有时会碰巧通过）。
        forged = PushedUpdate1(
            delta=P1.delta, st=P1.st, J=P1.J, F_J=P1.F_J,
            F_K=(P1.F_K[0] ^ 1, P1.F_K[1]), pi_K=P1.pi_K,
        )
        for name, node in cases.items():
            assert not node.apply_update(OP_MOD, forged).ok, name

    def test_换掉_K_被拒(self, session, R0, P1):
        bad = UpdateOp1("mod", [5, 6], [0, 0])
        assert not R0.apply_update(bad, P1).ok


class TestAddPush:
    def test_新摘要等于重新提交(self, session, P2, V2):
        assert P2.delta == com_prime(session.crs, V2)

    def test_长度加_2(self, P2):
        assert P2.delta.n == N0 + 2

    def test_发布者状态不变_下标集合扩大(self, session, R1, P2):
        assert (P2.st.Gamma[0], P2.st.Delta[0]) == (
            R1.st.Gamma[0], R1.st.Delta[0]
        )
        assert P2.J == tuple(range(N0 + 2))

    def test_没有更新见证(self, P2):
        assert P2.F_K == () and P2.pi_K is None

    def test_下标不在尾部时报错(self, session, R1):
        with pytest.raises(ValueError):
            R1.push_update(UpdateOp1("add", [20, 21], [0, 1]))


class TestAddApply:
    def test_客户端接受并算出同一个新摘要(self, session, R1, OP_ADD, P2, V2):
        ok, delta_p = ClientNode1("c", session, R1.delta).apply_update(
            OP_ADD, P2
        )
        assert ok and delta_p == P2.delta == com_prime(session.crs, V2)

    def test_不持有新增块的节点状态被抬指数(self, session, R0, OP_MOD, P1,
                                            OP_ADD, P2):
        node = make_node(session, R0, [6, 7, 8], "disj")
        node, _ = apply_and_wrap(session, node, OP_MOD, P1)
        new, res = apply_and_wrap(session, node, OP_ADD, P2)
        assert res.ok
        assert new.check_local_view()
        assert new.I == (6, 7, 8)
        assert new.st.Gamma != node.st.Gamma     # 指数被抬了

    def test_下标不在尾部被拒(self, session, R1, P2):
        bad = UpdateOp1("add", [20, 21], [0, 1])
        assert not ClientNode1("c", session, R1.delta).apply_update(
            bad, P2
        )[0]

    def test_只有长度检查_陈旧摘要也会被接受(self, session, R0, OP_ADD, P2, P1):
        """论文的 ``ClntNode.ApplyUpdate`` 对 ``add`` 只查长度。

        ``Υ_∆`` 是空的，客户端手里没有任何能验的东西，
        所以它无法察觉自己的摘要已经过期。这里把这个已知性质固定下来。
        """
        stale = ClientNode1("stale", session, R0.delta)
        ok, delta_p = stale.apply_update(OP_ADD, P2)
        assert ok
        assert delta_p != P2.delta          # 算出来的是另一个摘要


class TestDelPush:
    def test_新摘要就是_K_上的证据(self, session, P3):
        assert (P3.delta.A, P3.delta.B) == (P3.pi_K.Gamma[0], P3.pi_K.Delta[0])

    def test_等于重新提交(self, session, P3, V1):
        assert P3.delta == com_prime(session.crs, V1)

    def test_长度减_2(self, P3):
        assert P3.delta.n == N0

    def test_携带被删的旧值与证据(self, session, R2, P3, V2):
        assert P3.F_K == (V2[12], V2[13])
        assert ver_prime(session.crs, R2.delta, [12, 13], list(P3.F_K), P3.pi_K)

    def test_删不持有下标报错(self, session, R1):
        node = make_node(session, R1, [0, 1, 2])
        with pytest.raises(ValueError):
            node.push_update(UpdateOp1("del", [12, 13]))


class TestDelApply:
    @pytest.fixture(scope="class")
    def cases(self, session, R2):
        return {
            "I∩K=∅": make_node(session, R2, [0, 1, 2, 3], "disj"),
            "I∩K=K": make_node(session, R2, [10, 11, 12, 13], "over"),
            "I∩K=L": make_node(session, R2, [11, 12], "part"),
        }

    def test_客户端接受并算出同一个新摘要(self, session, R2, OP_DEL, P3, V1):
        ok, delta_p = ClientNode1("c", session, R2.delta).apply_update(
            OP_DEL, P3
        )
        assert ok and delta_p == P3.delta == com_prime(session.crs, V1)

    def test_三种情形的本地视图都更新正确(self, session, cases, OP_DEL, P3):
        for name, node in cases.items():
            new, res = apply_and_wrap(session, node, OP_DEL, P3, name)
            assert res.ok, name
            assert new.check_local_view(), name
            assert new.I == tuple(i for i in node.I if i not in (12, 13)), name

    def test_与_K_完全重合的节点状态不变(self, session, cases, OP_DEL, P3):
        old = cases["I∩K=K"]
        new, _ = apply_and_wrap(session, old, OP_DEL, P3)
        assert new.st.Gamma == old.st.Gamma
        assert new.I == (10, 11)

    def test_与_K_不相交的节点做一次_ShamirTrick(self, session, cases,
                                                OP_DEL, P3):
        old = cases["I∩K=∅"]
        new, _ = apply_and_wrap(session, old, OP_DEL, P3)
        assert new.st.Gamma != old.st.Gamma
        assert new.I == (0, 1, 2, 3)

    def test_下标不在尾部被拒(self, session, R2, P3):
        bad = UpdateOp1("del", [5, 6])
        assert not ClientNode1("c", session, R2.delta).apply_update(
            bad, P3
        )[0]

    def test_伪造证据被拒(self, session, R2, OP_DEL, P3):
        forged = PushedUpdate1(
            delta=P3.delta, st=P3.st, J=P3.J, F_J=P3.F_J,
            F_K=(P3.F_K[0] ^ 1, P3.F_K[1]), pi_K=P3.pi_K,
        )
        assert not R2.apply_update(OP_DEL, forged).ok


class TestUpdateChain:
    def test_一整条链走完之后根节点仍然有效(self, session, R3, V1):
        assert R3.check_local_view()
        assert R3.FI == V1
        assert R3.delta == com_prime(session.crs, V1)

    def test_客户端全程同步(self, session, R0, OP_MOD, P1, OP_ADD, P2,
                          OP_DEL, P3, V1):
        client = ClientNode1("c", session, R0.delta)
        for op, pushed in ((OP_MOD, P1), (OP_ADD, P2), (OP_DEL, P3)):
            ok, delta_p = client.apply_update(op, pushed)
            assert ok
            client = ClientNode1("c", session, delta_p)
        assert client.delta == com_prime(session.crs, V1)

    def test_每步之后检索都还能验证(self, session, R0, OP_MOD, P1, OP_ADD,
                                  P2, OP_DEL, P3):
        node = R0
        for op, pushed in ((OP_MOD, P1), (OP_ADD, P2), (OP_DEL, P3)):
            node, res = apply_and_wrap(session, node, op, pushed, "chain")
            assert res.ok
            client = ClientNode1("c", session, node.delta)
            F_Q, pi_Q = node.retrieve([0, 1, 2])
            assert client.ver_retrieve([0, 1, 2], F_Q, pi_Q)

    def test_每步之后_GetCreate_都还能用(self, session, R0, OP_MOD, P1,
                                       OP_ADD, P2):
        node, _ = apply_and_wrap(session, R0, OP_MOD, P1, "n")
        node, _ = apply_and_wrap(session, node, OP_ADD, P2, "n")
        derived, upsilon = node.create_from(list(range(6)))
        client = ClientNode1("c", session, node.delta)
        assert client.get_create(list(range(6)), upsilon)[0]
        assert derived.check_local_view()


# ---------------------------------------------------------------------------
# 5. 攻击面
# ---------------------------------------------------------------------------

class TestAttacks:
    def test_按见证对应的摘要做_mod_被接受(self, session, R0, OP_MOD, P1):
        assert ClientNode1("c", session, R0.delta).apply_update(OP_MOD, P1)[0]

    def test_mod_重放被拒(self, session, R0, OP_MOD, P1):
        """``mod`` 的 ``π_K`` 只对它签发时的那版摘要有效，重放一律被拒。

        这条对任何 ``I`` 都成立：拒绝发生在三种情形之前的那一步
        ``VC.Ver'(δ', K, F_K, π_K)``，与其他位置无关。
        """
        once = R0.apply_update(OP_MOD, P1)
        assert once.ok
        assert not ClientNode1("c", session, once.delta).apply_update(
            OP_MOD, P1
        )[0]
        for I in ([2, 3, 4, 5], [6, 7, 8], [4, 5, 6]):
            node = make_node(session, R0, I, "n")
            first = node.apply_update(OP_MOD, P1)
            assert first.ok, I
            assert not node_of(session, first).apply_update(OP_MOD, P1).ok, I

    def test_陈旧摘要上做_del_被拒(self, session, R0, OP_DEL, P3):
        assert not ClientNode1("c", session, R0.delta).apply_update(
            OP_DEL, P3
        )[0]

    def test_重复_del_被拒(self, session, R3, OP_DEL, P3):
        assert not ClientNode1("c", session, R3.delta).apply_update(
            OP_DEL, P3
        )[0]

    def test_用别的文件的证据签名被拒(self, session, R0, V1):
        """把 mod 的 ``Υ_∆`` 换成另一份文件算出来的证据。"""
        other_delta = com_prime(session.crs, V1)
        forged = PushedUpdate1(
            delta=other_delta, st=R0.st, J=R0.I, F_J=R0.FI,
            F_K=(0, 0), pi_K=R0.st,
        )
        assert not ClientNode1("c", session, R0.delta).apply_update(
            UpdateOp1("mod", [3, 4], [0, 0]), forged
        )[0]

    def test_空_K_的更新没有意义(self):
        with pytest.raises(ValueError):
            UpdateOp1("mod", [])
        with pytest.raises(ValueError):
            UpdateOp1("add", [], [])
        with pytest.raises(ValueError):
            UpdateOp1("del", [])

    def test_未知_op_报错(self):
        with pytest.raises(ValueError):
            UpdateOp1("copy", [0])

    def test_del_不允许带新值(self):
        with pytest.raises(ValueError):
            UpdateOp1("del", [0], [1])

    def test_mod_的新值长度必须与_K_一致(self):
        with pytest.raises(ValueError):
            UpdateOp1("mod", [0, 1], [1])
