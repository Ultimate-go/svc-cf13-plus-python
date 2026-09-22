<<<<<<< HEAD
"""VDS 应用层测试 —— 论文 §8.2 的 ``VDS2``。

覆盖需求里描述的那条完整链路：

    文件 → 切块 → 分发到多台服务器 → 检索若干部分 →
    服务器返回内容 + 证据 → 聚合多份证据成一个 → 客户端验证这一个

以及三类攻击：服务器篡改内容、伪造证据、节点之间串通。
"""

from __future__ import annotations

import pytest

from svc import DeterministicRNG
from vds import (
    Digest,
    LocalView,
    StorageNode,
    VDSSession,
    blocks_for_length,
    join_blocks,
    l_for_block_bytes,
    split_bytes,
)

BLOCK_BYTES = 16
N_MAX = 16
L = BLOCK_BYTES * 8


@pytest.fixture(scope="module")
def session():
    return VDSSession(
        n_max=N_MAX,
        l=L,
        lambda_bits=16,
        modulus_bits=512,
        seed=b"pytest-vds",
    )


@pytest.fixture(scope="module")
def file_setup(session):
    """建一个正好铺满 n_max 块的文件并分发到 4 个节点。"""
    payload = bytes(DeterministicRNG(b"file").read_bytes(N_MAX * BLOCK_BYTES - 3))
    delta, crs_n, values, nbytes = session.commit_bytes(payload, BLOCK_BYTES)
    nodes = session.distribute(
        delta,
        values,
        [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]],
        crs_n=crs_n,
    )
    return {
        "payload": payload,
        "delta": delta,
        "crs_n": crs_n,
        "values": values,
        "nbytes": nbytes,
        "nodes": nodes,
    }


# ---------------------------------------------------------------------------
# 编码
# ---------------------------------------------------------------------------

class TestEncoding:
    def test_往返一致(self):
        for size in (0, 1, 15, 16, 17, 31, 32, 100, 250):
            data = bytes(range(256))[:size] if size else b""
            blocks = split_bytes(data, BLOCK_BYTES)
            assert join_blocks(blocks, BLOCK_BYTES, len(data)) == data

    def test_块数计算(self):
        assert blocks_for_length(0, 16) == 0
        assert blocks_for_length(1, 16) == 1
        assert blocks_for_length(16, 16) == 1
        assert blocks_for_length(17, 16) == 2
        assert blocks_for_length(250, 16) == 16

    def test_每块都在_l_位以内(self):
        data = bytes(DeterministicRNG(b"x").read_bytes(250))
        L_ = l_for_block_bytes(BLOCK_BYTES)
        for v in split_bytes(data, BLOCK_BYTES):
            assert 0 <= v < (1 << L_)

    def test_截断长度不足时报错(self):
        with pytest.raises(ValueError):
            join_blocks([1, 2], BLOCK_BYTES, 1000)


# ---------------------------------------------------------------------------
# Bootstrap 与承诺
# ---------------------------------------------------------------------------

class TestBootstrapCommit:
    def test_bootstrap_的初始摘要(self, session):
        d = session.bootstrap()
        assert d.n == 0 and d.U == 1 and d.C == session.crs.g

    def test_摘要是常量大小(self, file_setup, session):
        d = file_setup["delta"]
        assert d.n == N_MAX
        assert d.U.bit_length() <= 512
        assert d.C.bit_length() <= 512

    def test_超过容量报错(self, session):
        with pytest.raises(ValueError, match="超过了会话上限"):
            session.commit_file([1] * (N_MAX + 1))

    def test_空文件报错(self, session):
        with pytest.raises(ValueError):
            session.commit_file([])

    def test_值超范围报错(self, session):
        with pytest.raises(ValueError, match="超出"):
            session.commit_file([1 << L])

    def test_块大小与_l_不匹配报错(self, session):
        with pytest.raises(ValueError, match="不匹配"):
            session.commit_bytes(b"x" * 32, 8)

    def test_可复现(self, session):
        payload = b"reproducible"
        a = session.commit_bytes(payload, BLOCK_BYTES)[0]
        b = session.commit_bytes(payload, BLOCK_BYTES)[0]
        assert a == b


# ---------------------------------------------------------------------------
# 分发
# ---------------------------------------------------------------------------

class TestDistribute:
    def test_每个节点都通过本地视图检查(self, file_setup):
        for node in file_setup["nodes"]:
            assert node.check_local_view(), f"{node.node_id} 本地视图不合法"

    def test_分配重叠报错(self, session, file_setup):
        with pytest.raises(ValueError, match="重叠"):
            session.distribute(
                file_setup["delta"],
                file_setup["values"],
                [[0, 1, 2, 3], [3, 4, 5, 6]],
                crs_n=file_setup["crs_n"],
            )

    def test_分配越界报错(self, session, file_setup):
        with pytest.raises(ValueError, match="越界"):
            session.distribute(
                file_setup["delta"],
                file_setup["values"],
                [[0, 999]],
                crs_n=file_setup["crs_n"],
            )


# ---------------------------------------------------------------------------
# 主流程：检索 → 聚合 → 验证
# ---------------------------------------------------------------------------

class TestRetrieveAggregateVerify:
    def test_单节点检索(self, session, file_setup):
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])
        F_Q, certs, used = session.retrieve_from(nodes, [0, 1])

        Q, vals, report = client.retrieve_and_verify(certs)
        assert report.ok, report.message
        assert vals == F_Q
        assert len(used) == 1

    def test_跨多节点检索并聚合成一个证明(self, session, file_setup):
        """需求的核心：从多台服务器取回，聚合成**一个**证据再验证。"""
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])

        Q = [1, 2, 9, 10, 13]  # 跨 node-0 / node-2 / node-3
        F_Q, certs, used = session.retrieve_from(nodes, Q)
        assert len(certs) == 3

        pi_K = client.aggregate_certificates(certs)
        # 聚合后是一个证明
        assert set(pi_K.I) == set(Q)

        values = file_setup["values"]
        report = client.ver_retrieve(Q, [values[i] for i in Q], pi_K)
        assert report.ok, report.message

    def test_聚合结果与直接打开逐位相同(self, session, file_setup):
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])
        Q = [1, 2, 9, 10, 13]
        _, certs, _ = session.retrieve_from(nodes, Q)
        pi_K = client.aggregate_certificates(certs)

        from svc import open_subvector

        values = file_setup["values"]
        direct = open_subvector(
            file_setup["crs_n"], Q, [values[i] for i in Q], values
        )
        assert pi_K.S_I == direct.S_I
        assert pi_K.Lambda_I == direct.Lambda_I

    def test_全量检索并字节级恢复(self, session, file_setup):
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])

        F_all, certs, _ = session.retrieve_from(nodes, list(range(N_MAX)))
        Q, vals, report = client.retrieve_and_verify(certs)
        assert report.ok

        recovered = join_blocks(list(vals), BLOCK_BYTES, file_setup["nbytes"])
        assert recovered == file_setup["payload"]

    def test_没有节点覆盖时报错(self, session, file_setup):
        nodes = file_setup["nodes"][:2]  # 只覆盖 0..7
        with pytest.raises(ValueError, match="没有节点覆盖"):
            session.retrieve_from(nodes, [0, 15])

    def test_单份凭证直接验证(self, session, file_setup):
        node = file_setup["nodes"][0]
        client = session.make_client(file_setup["delta"])
        F_Q, pi_Q = node.retrieve([1, 2])
        assert client.ver_retrieve([1, 2], list(F_Q), pi_Q).ok

    def test_单份凭证被改值就失败(self, session, file_setup):
        node = file_setup["nodes"][0]
        client = session.make_client(file_setup["delta"])
        F_Q, pi_Q = node.retrieve([1, 2])
        lying = list(F_Q)
        lying[0] += 1
        assert not client.ver_retrieve([1, 2], lying, pi_Q).ok


# ---------------------------------------------------------------------------
# 攻击场景
# ---------------------------------------------------------------------------

class TestAttacks:
    def test_服务器篡改内容(self, session, file_setup):
        node = file_setup["nodes"][1]
        client = session.make_client(file_setup["delta"])

        tampered = list(node.FI)
        tampered[0] ^= 0xFF
        evil = StorageNode(
            "evil",
            session,
            LocalView(
                delta=node.view.delta,
                st=node.st,          # 证据原封不动
                I=node.I,
                FI=tuple(tampered),
            ),
        )
        F_Q, pi_Q = evil.retrieve([node.I[0]])
        report = client.ver_retrieve([node.I[0]], list(F_Q), pi_Q)
        assert not report.ok

    def test_服务器伪造证据(self, session, file_setup):
        node = file_setup["nodes"][1]
        client = session.make_client(file_setup["delta"])

        from svc import Opening

        evil = StorageNode(
            "forger",
            session,
            LocalView(
                delta=node.view.delta,
                st=Opening(
                    S_I=(node.st.S_I * 7) % session.crs.N,
                    Lambda_I=node.st.Lambda_I,
                    I=node.st.I,
                ),
                I=node.I,
                FI=node.FI,
            ),
        )
        F_Q, pi_Q = evil.retrieve([node.I[0]])
        report = client.ver_retrieve([node.I[0]], list(F_Q), pi_Q)
        assert not report.ok

    def test_节点偷偷丢掉一部分数据(self):
        """丢掉部分数据后本地视图立刻不合法。"""
        s = VDSSession(n_max=8, l=L, lambda_bits=16, modulus_bits=512, seed=b"drop")
        payload = bytes(DeterministicRNG(b"d").read_bytes(8 * BLOCK_BYTES))
        delta, crs_n, values, _ = s.commit_bytes(payload, BLOCK_BYTES)
        node = s.distribute(delta, values, [list(range(8))], crs_n=crs_n)[0]
        assert node.check_local_view()

        # 声称只持有前 4 块，但没重新拆证据
        bad = StorageNode(
            "liar",
            s,
            LocalView(
                delta=node.view.delta,
                st=node.st,
                I=node.I[:4],
                FI=node.FI[:4],
            ),
        )
        assert not bad.check_local_view()

    def test_用正确的_rmv_storage_丢数据仍然是合法的(self):
        s = VDSSession(n_max=8, l=L, lambda_bits=16, modulus_bits=512, seed=b"drop2")
        payload = bytes(DeterministicRNG(b"d2").read_bytes(8 * BLOCK_BYTES))
        delta, crs_n, values, _ = s.commit_bytes(payload, BLOCK_BYTES)
        node = s.distribute(delta, values, [list(range(8))], crs_n=crs_n)[0]

        lean = node.rmv_storage([4, 5, 6, 7])
        assert lean.I == (0, 1, 2, 3)
        assert lean.check_local_view()
        # 还能正常响应检索
        client = s.make_client(delta)
        F_Q, pi_Q = lean.retrieve([1, 3])
        assert client.ver_retrieve([1, 3], list(F_Q), pi_Q).ok


# ---------------------------------------------------------------------------
# 节点间合并
# ---------------------------------------------------------------------------

class TestNodeMerge:
    def test_add_storage_合并后仍是合法节点(self, session, file_setup):
        a, b = file_setup["nodes"][0], file_setup["nodes"][1]
        merged = a.add_storage(b)
        assert merged.I == (0, 1, 2, 3, 4, 5, 6, 7)
        assert merged.check_local_view()

    def test_合并后能响应跨原节点的检索(self, session, file_setup):
        a, b = file_setup["nodes"][0], file_setup["nodes"][1]
        merged = a.add_storage(b)
        client = session.make_client(file_setup["delta"])
        F_Q, pi_Q = merged.retrieve([1, 6])
        assert client.ver_retrieve([1, 6], list(F_Q), pi_Q).ok

    def test_合并重叠节点报错(self, session, file_setup):
        a = file_setup["nodes"][0]
        with pytest.raises(ValueError, match="不相交"):
            a.add_storage(a)

    def test_先拆再合(self, session, file_setup):
        a, b = file_setup["nodes"][0], file_setup["nodes"][1]
        merged = a.add_storage(b)
        split = merged.rmv_storage([4, 5, 6, 7])
        assert split.I == (0, 1, 2, 3)
        assert split.check_local_view()

    def test_摘要不同不能合并(self, session, file_setup):
        a = file_setup["nodes"][0]
        other = VDSSession(n_max=4, l=L, lambda_bits=16, modulus_bits=512, seed=b"other")
        d2, c2, v2, _ = other.commit_bytes(b"x" * 64, BLOCK_BYTES)

        from svc import Opening

        foreign = StorageNode(
            "foreign",
            other,
            LocalView(delta=d2, st=Opening(1, 1, ()), I=(), FI=()),
        )
        with pytest.raises(ValueError, match="摘要不同"):
            a.add_storage(foreign)


# ---------------------------------------------------------------------------
# CreateFrom / GetCreate 属于 §8.1，不在 §8.2 里
# ---------------------------------------------------------------------------

class TestNotImplemented:
    def test_create_from_指向_vds1(self, session, file_setup):
        node = file_setup["nodes"][0]
        with pytest.raises(NotImplementedError, match="vds1"):
            node.create_from([0, 1])

    def test_get_create_指向_vds1(self, session, file_setup):
        client = session.make_client(file_setup["delta"])
        with pytest.raises(NotImplementedError, match="vds1"):
            client.get_create([0, 1])

    def test_vds1_里同时有这两个算法(self):
        """报错信息指的那个地方确实存在同名方法。"""
        from vds.vds1 import ClientNode1, StorageNode1

        assert callable(StorageNode1.create_from)
        assert callable(ClientNode1.get_create)


# ---------------------------------------------------------------------------
# 会话缓存
# ---------------------------------------------------------------------------

class TestSessionCache:
    def test_crs_n_缓存命中(self, session, file_setup):
        a = session.crs_n_for(file_setup["delta"])
        b = session.crs_n_for(file_setup["delta"])
        assert a is b

    def test_e_all_只算一次(self, session, file_setup):
        assert session.e_all_for(N_MAX) is session.e_all_for(N_MAX)

    def test_摘要的_U_被采纳(self, session, file_setup):
        """crs_n 里的 U_n 必须来自摘要，而不是重算 g^{e_[n]}。"""
        crs_n = session.crs_n_for(file_setup["delta"])
        assert crs_n.U_n == file_setup["delta"].U

    def test_空摘要取_crs_n_报错(self, session):
        with pytest.raises(ValueError):
            session.crs_n_for(session.bootstrap())
=======
"""VDS 应用层测试 —— 论文 §8.2 的 ``VDS2``。

覆盖需求里描述的那条完整链路：

    文件 → 切块 → 分发到多台服务器 → 检索若干部分 →
    服务器返回内容 + 证据 → 聚合多份证据成一个 → 客户端验证这一个

以及三类攻击：服务器篡改内容、伪造证据、节点之间串通。
"""

from __future__ import annotations

import pytest

from svc import DeterministicRNG
from vds import (
    Digest,
    LocalView,
    StorageNode,
    VDSSession,
    blocks_for_length,
    join_blocks,
    l_for_block_bytes,
    split_bytes,
)

BLOCK_BYTES = 16
N_MAX = 16
L = BLOCK_BYTES * 8


@pytest.fixture(scope="module")
def session():
    return VDSSession(
        n_max=N_MAX,
        l=L,
        lambda_bits=16,
        modulus_bits=512,
        seed=b"pytest-vds",
    )


@pytest.fixture(scope="module")
def file_setup(session):
    """建一个正好铺满 n_max 块的文件并分发到 4 个节点。"""
    payload = bytes(DeterministicRNG(b"file").read_bytes(N_MAX * BLOCK_BYTES - 3))
    delta, crs_n, values, nbytes = session.commit_bytes(payload, BLOCK_BYTES)
    nodes = session.distribute(
        delta,
        values,
        [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]],
        crs_n=crs_n,
    )
    return {
        "payload": payload,
        "delta": delta,
        "crs_n": crs_n,
        "values": values,
        "nbytes": nbytes,
        "nodes": nodes,
    }


# ---------------------------------------------------------------------------
# 编码
# ---------------------------------------------------------------------------

class TestEncoding:
    def test_往返一致(self):
        for size in (0, 1, 15, 16, 17, 31, 32, 100, 250):
            data = bytes(range(256))[:size] if size else b""
            blocks = split_bytes(data, BLOCK_BYTES)
            assert join_blocks(blocks, BLOCK_BYTES, len(data)) == data

    def test_块数计算(self):
        assert blocks_for_length(0, 16) == 0
        assert blocks_for_length(1, 16) == 1
        assert blocks_for_length(16, 16) == 1
        assert blocks_for_length(17, 16) == 2
        assert blocks_for_length(250, 16) == 16

    def test_每块都在_l_位以内(self):
        data = bytes(DeterministicRNG(b"x").read_bytes(250))
        L_ = l_for_block_bytes(BLOCK_BYTES)
        for v in split_bytes(data, BLOCK_BYTES):
            assert 0 <= v < (1 << L_)

    def test_截断长度不足时报错(self):
        with pytest.raises(ValueError):
            join_blocks([1, 2], BLOCK_BYTES, 1000)


# ---------------------------------------------------------------------------
# Bootstrap 与承诺
# ---------------------------------------------------------------------------

class TestBootstrapCommit:
    def test_bootstrap_的初始摘要(self, session):
        d = session.bootstrap()
        assert d.n == 0 and d.U == 1 and d.C == session.crs.g

    def test_摘要是常量大小(self, file_setup, session):
        d = file_setup["delta"]
        assert d.n == N_MAX
        assert d.U.bit_length() <= 512
        assert d.C.bit_length() <= 512

    def test_超过容量报错(self, session):
        with pytest.raises(ValueError, match="超过了会话上限"):
            session.commit_file([1] * (N_MAX + 1))

    def test_空文件报错(self, session):
        with pytest.raises(ValueError):
            session.commit_file([])

    def test_值超范围报错(self, session):
        with pytest.raises(ValueError, match="超出"):
            session.commit_file([1 << L])

    def test_块大小与_l_不匹配报错(self, session):
        with pytest.raises(ValueError, match="不匹配"):
            session.commit_bytes(b"x" * 32, 8)

    def test_可复现(self, session):
        payload = b"reproducible"
        a = session.commit_bytes(payload, BLOCK_BYTES)[0]
        b = session.commit_bytes(payload, BLOCK_BYTES)[0]
        assert a == b


# ---------------------------------------------------------------------------
# 分发
# ---------------------------------------------------------------------------

class TestDistribute:
    def test_每个节点都通过本地视图检查(self, file_setup):
        for node in file_setup["nodes"]:
            assert node.check_local_view(), f"{node.node_id} 本地视图不合法"

    def test_分配重叠报错(self, session, file_setup):
        with pytest.raises(ValueError, match="重叠"):
            session.distribute(
                file_setup["delta"],
                file_setup["values"],
                [[0, 1, 2, 3], [3, 4, 5, 6]],
                crs_n=file_setup["crs_n"],
            )

    def test_分配越界报错(self, session, file_setup):
        with pytest.raises(ValueError, match="越界"):
            session.distribute(
                file_setup["delta"],
                file_setup["values"],
                [[0, 999]],
                crs_n=file_setup["crs_n"],
            )


# ---------------------------------------------------------------------------
# 主流程：检索 → 聚合 → 验证
# ---------------------------------------------------------------------------

class TestRetrieveAggregateVerify:
    def test_单节点检索(self, session, file_setup):
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])
        F_Q, certs, used = session.retrieve_from(nodes, [0, 1])

        Q, vals, report = client.retrieve_and_verify(certs)
        assert report.ok, report.message
        assert vals == F_Q
        assert len(used) == 1

    def test_跨多节点检索并聚合成一个证明(self, session, file_setup):
        """需求的核心：从多台服务器取回，聚合成**一个**证据再验证。"""
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])

        Q = [1, 2, 9, 10, 13]  # 跨 node-0 / node-2 / node-3
        F_Q, certs, used = session.retrieve_from(nodes, Q)
        assert len(certs) == 3

        pi_K = client.aggregate_certificates(certs)
        # 聚合后是一个证明
        assert set(pi_K.I) == set(Q)

        values = file_setup["values"]
        report = client.ver_retrieve(Q, [values[i] for i in Q], pi_K)
        assert report.ok, report.message

    def test_聚合结果与直接打开逐位相同(self, session, file_setup):
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])
        Q = [1, 2, 9, 10, 13]
        _, certs, _ = session.retrieve_from(nodes, Q)
        pi_K = client.aggregate_certificates(certs)

        from svc import open_subvector

        values = file_setup["values"]
        direct = open_subvector(
            file_setup["crs_n"], Q, [values[i] for i in Q], values
        )
        assert pi_K.S_I == direct.S_I
        assert pi_K.Lambda_I == direct.Lambda_I

    def test_全量检索并字节级恢复(self, session, file_setup):
        nodes = file_setup["nodes"]
        client = session.make_client(file_setup["delta"])

        F_all, certs, _ = session.retrieve_from(nodes, list(range(N_MAX)))
        Q, vals, report = client.retrieve_and_verify(certs)
        assert report.ok

        recovered = join_blocks(list(vals), BLOCK_BYTES, file_setup["nbytes"])
        assert recovered == file_setup["payload"]

    def test_没有节点覆盖时报错(self, session, file_setup):
        nodes = file_setup["nodes"][:2]  # 只覆盖 0..7
        with pytest.raises(ValueError, match="没有节点覆盖"):
            session.retrieve_from(nodes, [0, 15])

    def test_单份凭证直接验证(self, session, file_setup):
        node = file_setup["nodes"][0]
        client = session.make_client(file_setup["delta"])
        F_Q, pi_Q = node.retrieve([1, 2])
        assert client.ver_retrieve([1, 2], list(F_Q), pi_Q).ok

    def test_单份凭证被改值就失败(self, session, file_setup):
        node = file_setup["nodes"][0]
        client = session.make_client(file_setup["delta"])
        F_Q, pi_Q = node.retrieve([1, 2])
        lying = list(F_Q)
        lying[0] += 1
        assert not client.ver_retrieve([1, 2], lying, pi_Q).ok


# ---------------------------------------------------------------------------
# 攻击场景
# ---------------------------------------------------------------------------

class TestAttacks:
    def test_服务器篡改内容(self, session, file_setup):
        node = file_setup["nodes"][1]
        client = session.make_client(file_setup["delta"])

        tampered = list(node.FI)
        tampered[0] ^= 0xFF
        evil = StorageNode(
            "evil",
            session,
            LocalView(
                delta=node.view.delta,
                st=node.st,          # 证据原封不动
                I=node.I,
                FI=tuple(tampered),
            ),
        )
        F_Q, pi_Q = evil.retrieve([node.I[0]])
        report = client.ver_retrieve([node.I[0]], list(F_Q), pi_Q)
        assert not report.ok

    def test_服务器伪造证据(self, session, file_setup):
        node = file_setup["nodes"][1]
        client = session.make_client(file_setup["delta"])

        from svc import Opening

        evil = StorageNode(
            "forger",
            session,
            LocalView(
                delta=node.view.delta,
                st=Opening(
                    S_I=(node.st.S_I * 7) % session.crs.N,
                    Lambda_I=node.st.Lambda_I,
                    I=node.st.I,
                ),
                I=node.I,
                FI=node.FI,
            ),
        )
        F_Q, pi_Q = evil.retrieve([node.I[0]])
        report = client.ver_retrieve([node.I[0]], list(F_Q), pi_Q)
        assert not report.ok

    def test_节点偷偷丢掉一部分数据(self):
        """丢掉部分数据后本地视图立刻不合法。"""
        s = VDSSession(n_max=8, l=L, lambda_bits=16, modulus_bits=512, seed=b"drop")
        payload = bytes(DeterministicRNG(b"d").read_bytes(8 * BLOCK_BYTES))
        delta, crs_n, values, _ = s.commit_bytes(payload, BLOCK_BYTES)
        node = s.distribute(delta, values, [list(range(8))], crs_n=crs_n)[0]
        assert node.check_local_view()

        # 声称只持有前 4 块，但没重新拆证据
        bad = StorageNode(
            "liar",
            s,
            LocalView(
                delta=node.view.delta,
                st=node.st,
                I=node.I[:4],
                FI=node.FI[:4],
            ),
        )
        assert not bad.check_local_view()

    def test_用正确的_rmv_storage_丢数据仍然是合法的(self):
        s = VDSSession(n_max=8, l=L, lambda_bits=16, modulus_bits=512, seed=b"drop2")
        payload = bytes(DeterministicRNG(b"d2").read_bytes(8 * BLOCK_BYTES))
        delta, crs_n, values, _ = s.commit_bytes(payload, BLOCK_BYTES)
        node = s.distribute(delta, values, [list(range(8))], crs_n=crs_n)[0]

        lean = node.rmv_storage([4, 5, 6, 7])
        assert lean.I == (0, 1, 2, 3)
        assert lean.check_local_view()
        # 还能正常响应检索
        client = s.make_client(delta)
        F_Q, pi_Q = lean.retrieve([1, 3])
        assert client.ver_retrieve([1, 3], list(F_Q), pi_Q).ok


# ---------------------------------------------------------------------------
# 节点间合并
# ---------------------------------------------------------------------------

class TestNodeMerge:
    def test_add_storage_合并后仍是合法节点(self, session, file_setup):
        a, b = file_setup["nodes"][0], file_setup["nodes"][1]
        merged = a.add_storage(b)
        assert merged.I == (0, 1, 2, 3, 4, 5, 6, 7)
        assert merged.check_local_view()

    def test_合并后能响应跨原节点的检索(self, session, file_setup):
        a, b = file_setup["nodes"][0], file_setup["nodes"][1]
        merged = a.add_storage(b)
        client = session.make_client(file_setup["delta"])
        F_Q, pi_Q = merged.retrieve([1, 6])
        assert client.ver_retrieve([1, 6], list(F_Q), pi_Q).ok

    def test_合并重叠节点报错(self, session, file_setup):
        a = file_setup["nodes"][0]
        with pytest.raises(ValueError, match="不相交"):
            a.add_storage(a)

    def test_先拆再合(self, session, file_setup):
        a, b = file_setup["nodes"][0], file_setup["nodes"][1]
        merged = a.add_storage(b)
        split = merged.rmv_storage([4, 5, 6, 7])
        assert split.I == (0, 1, 2, 3)
        assert split.check_local_view()

    def test_摘要不同不能合并(self, session, file_setup):
        a = file_setup["nodes"][0]
        other = VDSSession(n_max=4, l=L, lambda_bits=16, modulus_bits=512, seed=b"other")
        d2, c2, v2, _ = other.commit_bytes(b"x" * 64, BLOCK_BYTES)

        from svc import Opening

        foreign = StorageNode(
            "foreign",
            other,
            LocalView(delta=d2, st=Opening(1, 1, ()), I=(), FI=()),
        )
        with pytest.raises(ValueError, match="摘要不同"):
            a.add_storage(foreign)


# ---------------------------------------------------------------------------
# CreateFrom / GetCreate 不在本方案的能力范围内
# ---------------------------------------------------------------------------

class TestNotImplemented:
    def test_create_from_明确报错(self, session, file_setup):
        node = file_setup["nodes"][0]
        with pytest.raises(NotImplementedError, match="派生新文件"):
            node.create_from([0, 1])

    def test_get_create_明确报错(self, session, file_setup):
        client = session.make_client(file_setup["delta"])
        with pytest.raises(NotImplementedError, match="派生新文件"):
            client.get_create([0, 1])


# ---------------------------------------------------------------------------
# 会话缓存
# ---------------------------------------------------------------------------

class TestSessionCache:
    def test_crs_n_缓存命中(self, session, file_setup):
        a = session.crs_n_for(file_setup["delta"])
        b = session.crs_n_for(file_setup["delta"])
        assert a is b

    def test_e_all_只算一次(self, session, file_setup):
        assert session.e_all_for(N_MAX) is session.e_all_for(N_MAX)

    def test_摘要的_U_被采纳(self, session, file_setup):
        """crs_n 里的 U_n 必须来自摘要，而不是重算 g^{e_[n]}。"""
        crs_n = session.crs_n_for(file_setup["delta"])
        assert crs_n.U_n == file_setup["delta"].U

    def test_空摘要取_crs_n_报错(self, session):
        with pytest.raises(ValueError):
            session.crs_n_for(session.bootstrap())
>>>>>>> main
