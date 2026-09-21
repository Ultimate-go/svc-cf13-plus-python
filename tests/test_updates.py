"""文件更新操作测试 —— 论文 §8.2 的 ``PushUpdate`` / ``ApplyUpdate``。

每个用例都做同一件事：**执行一次更新，然后检查整个系统还是自洽的** ——

1. 每个节点的「本地视图」仍然合法（即 :func:`svc.verify` 通过）；
2. 客户端用新摘要能检索任意子集并通过验证；
3. 内容确实按预期变了（该改的改了、该删的没了、该加的加上了）。

这三条一旦同时成立，更新公式就**不可能错** —— 因为 :func:`svc.verify`
是独立实现，它不关心更新是怎么算出来的。

测试用 12 块的文件（``n_max = 16``），留出 4 个位置给 ``add`` 用。
"""

from __future__ import annotations

import pytest

from svc import add_back, disagg, e_of
from vds import VDSSession, join_blocks
from vds.updates import update_append, update_modify, update_truncate

BLOCK_BYTES = 16
N_MAX = 16
N_BLOCKS = 12
SPLIT = 6            # node-0 拿 [0,6)，node-1 拿 [6,12)


def make_env(seed=b"updates"):
    """建一个 12 块的文件，分给 2 台服务器，各持 6 块。"""
    s = VDSSession(
        n_max=N_MAX, l=BLOCK_BYTES * 8, lambda_bits=16,
        modulus_bits=512, seed=seed,
    )
    payload = bytes((i * 7 + 3) % 256 for i in range(N_BLOCKS * BLOCK_BYTES))
    delta, crs_n, values, nbytes = s.commit_bytes(payload, BLOCK_BYTES)
    nodes = s.distribute(
        delta, values,
        [list(range(0, SPLIT)), list(range(SPLIT, N_BLOCKS))],
        crs_n=crs_n,
    )
    assert delta.n == N_BLOCKS
    return s, delta, values, nodes, nbytes


def assert_all_valid(nodes):
    for nd in nodes:
        assert nd.check_local_view(), f"{nd.node_id} 的本地视图不再合法"


def assert_retrievable(s, delta, nodes, probes):
    """对若干组下标做「检索 → 聚合 → 验证」，全部应当通过。"""
    client = s.make_client(delta)
    for Q in probes:
        try:
            F_Q, certs, _ = s.retrieve_from(nodes, list(Q))
        except ValueError:
            continue  # 该区间不可达，跳过
        _, vals, report = client.retrieve_and_verify(certs)
        assert report.ok, f"Q = {Q} 检索后验证失败: {report.message}"


# ---------------------------------------------------------------------------
# op = mod
# ---------------------------------------------------------------------------

class TestModify:
    def test_改值后系统仍然自洽(self):
        s, delta, values, nodes, _ = make_env()

        K = [0, 1, 2]                      # 全在 node-0 手里
        F_new = [(values[i] + 12345) % (1 << 128) for i in K]
        rec = update_modify(s, delta, nodes, K, F_new)

        assert rec.new_delta.n == delta.n, "mod 不应改变长度"
        assert rec.new_delta.U == delta.U, "mod 不应改变 U"
        assert rec.new_delta.C != delta.C, "改了值，承诺必须变"

        assert_all_valid(rec.new_nodes)
        assert_retrievable(s, rec.new_delta, rec.new_nodes,
                           [(0,), (0, 1, 2), (4, 5), (0, 6), (9, 10)])

    def test_跨节点改值(self):
        """改动横跨两台服务器：一台需要修正 Λ，另一台不需要。"""
        s, delta, values, nodes, _ = make_env()

        K = [3, 4, 9, 10]                  # 3,4 在 node-0；9,10 在 node-1
        F_new = [(values[i] ^ 0xFF) % (1 << 128) for i in K]
        rec = update_modify(s, delta, nodes, K, F_new)

        assert_all_valid(rec.new_nodes)
        assert_retrievable(s, rec.new_delta, rec.new_nodes,
                           [(3, 4), (9, 10), (3, 4, 9, 10), (5, 11)])

    def test_持有被改位置的节点状态不变(self):
        """Λ_I 只含 j ∉ I 的值，所以改动落在 I 内的位置不影响该节点的 Λ。"""
        s, delta, values, nodes, _ = make_env()
        K = [0, 1]
        F_new = [(values[i] + 7) % (1 << 128) for i in K]
        rec = update_modify(s, delta, nodes, K, F_new)

        before = {nd.node_id: nd.st for nd in nodes}
        checked = 0
        for nd in rec.new_nodes:
            if set(K) <= set(nd.I):
                old = before[nd.node_id]
                assert nd.st.S_I == old.S_I
                assert nd.st.Lambda_I == old.Lambda_I, (
                    f"{nd.node_id} 持有全部被改位置，Λ 不该变"
                )
                checked += 1
        assert checked >= 1, "应当至少有一个节点完全持有 K"

    def test_值真的变了(self):
        s, delta, values, nodes, _ = make_env()
        K = [4]
        F_new = [(values[4] + 999999) % (1 << 128)]
        rec = update_modify(s, delta, nodes, K, F_new)

        holder = next(nd for nd in rec.new_nodes if 4 in nd.I)
        F_check, _ = holder.retrieve([4])
        assert F_check == tuple(F_new)

    def test_非法输入(self):
        s, delta, values, nodes, _ = make_env()
        with pytest.raises(ValueError):
            update_modify(s, delta, nodes, [], [])
        with pytest.raises(ValueError):
            update_modify(s, delta, nodes, [0, 1], [1])
        with pytest.raises(ValueError):
            update_modify(s, delta, nodes, [999], [1])


# ---------------------------------------------------------------------------
# op = add
# ---------------------------------------------------------------------------

class TestAppend:
    def test_追加后系统仍然自洽(self):
        s, delta, values, nodes, _ = make_env()

        F_new = [111, 222, 333]
        rec = update_append(s, delta, nodes, F_new)

        assert rec.new_delta.n == delta.n + 3
        assert rec.new_delta.U != delta.U, "追加位置必须改变 U"
        assert rec.new_delta.C != delta.C

        assert_all_valid(rec.new_nodes)
        assert_retrievable(s, rec.new_delta, rec.new_nodes,
                           [(0,), (0, 12), (12, 13, 14), (6, 12, 14)])

    def test_新位置的内容确实可检索(self):
        s, delta, values, nodes, _ = make_env()
        F_new = [42, 43]
        rec = update_append(s, delta, nodes, F_new)

        client = s.make_client(rec.new_delta)
        F_Q, certs, _ = s.retrieve_from(rec.new_nodes, [12, 13])
        assert F_Q == tuple(F_new)
        _, _, report = client.retrieve_and_verify(certs)
        assert report.ok

    def test_新节点的证明就是旧摘要(self):
        """π_K^new = (U, C) —— 因为「除 K 之外的部分」就是旧文件。"""
        s, delta, values, nodes, _ = make_env()
        rec = update_append(s, delta, nodes, [7, 8])

        fresh = rec.new_nodes[-1]
        assert set(fresh.I) == {12, 13}
        assert fresh.st.S_I == delta.U
        assert fresh.st.Lambda_I == delta.C

    def test_摘要侧的推导与_add_back_一致(self):
        """U' = U^{e_K}，C' = 对 (U, C) 顺序 add_back 的结果。"""
        s, delta, values, nodes, _ = make_env()
        F_new = [7, 8]
        rec = update_append(s, delta, nodes, F_new)

        pg, N = s.crs.primegen, s.crs.N
        K = (12, 13)
        e_K = e_of(pg, K)
        assert rec.new_delta.U == pow(delta.U, e_K, N)

        S, Lam = delta.U, delta.C
        for j, v in zip(K, F_new):
            S, Lam = add_back(S, Lam, pg.get(j), v, N)
        assert (rec.new_delta.U, rec.new_delta.C) == (S, Lam)

    def test_超过会话上限(self):
        s, delta, values, nodes, _ = make_env()
        with pytest.raises(ValueError, match="超过会话上限"):
            update_append(s, delta, nodes, [1, 2, 3, 4, 5])  # 12 + 5 > 16

    def test_刚好用满上限(self):
        s, delta, values, nodes, _ = make_env()
        rec = update_append(s, delta, nodes, [1, 2, 3, 4])   # 12 + 4 = 16
        assert rec.new_delta.n == N_MAX
        assert_all_valid(rec.new_nodes)


# ---------------------------------------------------------------------------
# op = del
# ---------------------------------------------------------------------------

class TestTruncate:
    def test_删末尾后系统仍然自洽(self):
        s, delta, values, nodes, _ = make_env()

        K = [10, 11]                       # node-1 持有
        rec = update_truncate(s, delta, nodes, K)

        assert rec.new_delta.n == delta.n - 2

        # 新摘要必须就是 π_K = d(v \ K)
        holder = next(nd for nd in nodes if set(K) <= set(nd.I))
        pi_K = disagg(s.crs_n_for(delta), list(holder.I), list(holder.FI),
                      holder.st, K)
        assert rec.new_delta.U == pi_K.S_I
        assert rec.new_delta.C == pi_K.Lambda_I

        assert all(nd.I for nd in rec.new_nodes)
        assert_all_valid(rec.new_nodes)
        assert_retrievable(s, rec.new_delta, rec.new_nodes,
                           [(0,), (5,), (0, 5), (3, 4)])

    def test_持有被删区间的节点状态不变(self):
        s, delta, values, nodes, _ = make_env()
        K = [10, 11]
        rec = update_truncate(s, delta, nodes, K)

        holder = next(nd for nd in nodes if set(K) <= set(nd.I))
        after = next(nd for nd in rec.new_nodes if nd.node_id == holder.node_id)
        assert after.st.S_I == holder.st.S_I
        assert after.st.Lambda_I == holder.st.Lambda_I, (
            "K ⊆ I 时 (S_I, Λ_I) 一个字都不该改"
        )
        assert set(after.I) == set(holder.I) - set(K)

    def test_不持有被删区间的节点做一次agg(self):
        s, delta, values, nodes, _ = make_env()
        K = [10, 11]
        rec = update_truncate(s, delta, nodes, K)

        other = next(nd for nd in nodes if not (set(K) & set(nd.I)))
        after = next(nd for nd in rec.new_nodes if nd.node_id == other.node_id)
        assert after.I == other.I, "不相交的节点下标集合不变"
        assert after.st != other.st, "但状态应当变成 agg(π_I, π_K)"

    def test_删光一个节点后它下线(self):
        s, delta, values, nodes, _ = make_env()
        rec = update_truncate(s, delta, nodes, list(range(SPLIT, N_BLOCKS)))
        ids = [nd.node_id for nd in rec.new_nodes]
        assert "node-1" not in ids, "node-1 的数据被删光了，应当下线"
        assert "node-0" in ids
        assert rec.new_delta.n == SPLIT
        assert_all_valid(rec.new_nodes)
        assert_retrievable(s, rec.new_delta, rec.new_nodes, [(0,), (5,), (2, 4)])

    def test_只能删末尾(self):
        s, delta, values, nodes, _ = make_env()
        with pytest.raises(ValueError, match="末尾"):
            update_truncate(s, delta, nodes, [0, 1])

    def test_删_1_个位置(self):
        s, delta, values, nodes, _ = make_env()
        rec = update_truncate(s, delta, nodes, [11])
        assert rec.new_delta.n == 11
        assert_all_valid(rec.new_nodes)
        assert_retrievable(s, rec.new_delta, rec.new_nodes, [(0,), (10,), (0, 10)])

    def test_删的位置必须有人持有(self):
        s, delta, values, nodes, _ = make_env()
        # 让 node-1 只留前 3 个位置，于是末尾没人持有了
        lean = [nodes[0], nodes[1].rmv_storage([9, 10, 11])]
        with pytest.raises(ValueError, match="没有任何节点"):
            update_truncate(s, delta, lean, [10, 11])


# ---------------------------------------------------------------------------
# 连续多次更新
# ---------------------------------------------------------------------------

class TestChainedUpdates:
    def test_改加改删连做四轮(self):
        """更新必须能反复做 —— 并且每一轮之后都要自洽。"""
        s, delta, values, nodes, _ = make_env()

        # 1) 改
        rec = update_modify(s, delta, nodes, [0, 1], [10, 20])
        delta, nodes = rec.new_delta, rec.new_nodes
        assert_all_valid(nodes)

        # 2) 加（n_max=16，当前 12，加 2 → 14）
        rec = update_append(s, delta, nodes, [30, 40])
        delta, nodes = rec.new_delta, rec.new_nodes
        assert delta.n == 14
        assert_all_valid(nodes)
        assert_retrievable(s, delta, nodes, [(0,), (12, 13), (1, 13)])

        # 3) 再改（包括新加的位置）
        rec = update_modify(s, delta, nodes, [13], [99])
        delta, nodes = rec.new_delta, rec.new_nodes
        assert_all_valid(nodes)
        assert_retrievable(s, delta, nodes, [(13,), (0, 13)])

        # 4) 删掉刚追加的两个
        rec = update_truncate(s, delta, nodes, [12, 13])
        delta, nodes = rec.new_delta, rec.new_nodes
        assert delta.n == 12
        assert_all_valid(nodes)
        assert_retrievable(s, delta, nodes, [(0,), (11,), (5, 11), (1, 2)])

    def test_内容正确性贯穿多轮更新(self):
        """最后一轮结束后，把整个文件取回来，逐字节核对期望内容。"""
        s, delta, values, nodes, _ = make_env()
        expected = list(values)

        rec = update_modify(s, delta, nodes, [2, 3], [777, 888])
        delta, nodes = rec.new_delta, rec.new_nodes
        expected[2], expected[3] = 777, 888

        rec = update_append(s, delta, nodes, [555])
        delta, nodes = rec.new_delta, rec.new_nodes
        expected.append(555)

        rec = update_truncate(s, delta, nodes, [12])
        delta, nodes = rec.new_delta, rec.new_nodes
        expected.pop()

        assert delta.n == len(expected)
        assert_all_valid(nodes)

        F_all, certs, _ = s.retrieve_from(nodes, list(range(delta.n)))
        client = s.make_client(delta)
        _, vals, report = client.retrieve_and_verify(certs)
        assert report.ok
        assert list(vals) == expected

        raw = join_blocks(list(vals), BLOCK_BYTES)
        want = b"".join(int(v).to_bytes(BLOCK_BYTES, "big") for v in expected)
        assert raw == want

    def test_连续追加到上限(self):
        s, delta, values, nodes, _ = make_env()
        for extra in ([1], [2, 3], [4]):
            rec = update_append(s, delta, nodes, extra)
            delta, nodes = rec.new_delta, rec.new_nodes
            assert_all_valid(nodes)
        assert delta.n == N_MAX
        assert_retrievable(s, delta, nodes, [(0,), (15,), (0, 15), (7, 8)])
