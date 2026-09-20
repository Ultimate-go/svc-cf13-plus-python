"""附录 D.1 的存储证明（``PoS-Challenge`` / ``PoS-Prove`` / ``PoS-Aggregate`` / ``PoS-Ver``）测试。

与「检索→聚合→验证」的区别在于验的是**收齐性**：
挑战点名 ``λ_pos`` 个下标，只有全部拿齐 ``b`` 才为 1。
所以这里的攻击面也分成两类：

* **少给** —— 某节点装死或只答一部分 → ``Q ≠ r``，验证报「挑战未收齐」；
* **给假的** —— 篡改内容或伪造证据 → 聚合阶段的 ``ShamirTrick`` 同源自检直接拒绝，
  连一份可验证的假证明都拼不出来。
"""

from __future__ import annotations

import pytest

from svc import Opening
from vds import LocalView, StorageNode, VDSSession
from vds.pos import (
    Challenge,
    PoSProof,
    parallel_pos_challenge,
    parallel_pos_verify,
    pos_aggregate,
    pos_aggregate_all,
    pos_challenge,
    pos_ver,
)

BLOCK_BYTES = 4
N_MAX = 64
N_BLOCKS = 32
LAMBDA_POS = 8


@pytest.fixture(scope="module")
def session():
    return VDSSession(
        n_max=N_MAX, l=BLOCK_BYTES * 8, lambda_bits=16,
        modulus_bits=256, seed=b"pytest-pos",
    )


@pytest.fixture(scope="module")
def deployed(session):
    """一个铺满 32 块的文件 + 4 个交错持有数据的节点。"""
    delta, crs_n, values, _ = session.commit_bytes(bytes(range(64)) * 2, BLOCK_BYTES)
    groups = [list(range(i, N_BLOCKS, 4)) for i in range(4)]
    nodes = session.distribute(delta, values, groups)
    return {
        "delta": delta, "crs_n": crs_n, "values": values,
        "nodes": nodes, "client": session.make_client(delta),
    }


def _tampered(node: StorageNode, session, *, forge_proof: bool = False) -> StorageNode:
    """造一个「内容被改」或「证据被伪造」的节点。"""
    v = node.view
    if forge_proof:
        st = Opening((v.st.S_I * 7919) % session.crs.N, v.st.Lambda_I, v.st.I)
        fi = v.FI
    else:
        st = v.st
        fi = (v.FI[0] ^ 0xFF,) + v.FI[1:]
    return StorageNode(f"{node.node_id}-evil", session, LocalView(v.delta, st, v.I, fi))


# ---------------------------------------------------------------------------
# 挑战
# ---------------------------------------------------------------------------

class TestChallenge:
    def test_大小与范围(self):
        c = pos_challenge(100, 12)
        assert c.size == 12 and c.n == 100
        assert len(set(c.indices)) == 12          # 不放回，无重复
        assert all(0 <= i < 100 for i in c.indices)
        assert list(c.indices) == sorted(c.indices)

    def test_n_小于lambda时取满(self):
        assert pos_challenge(3, 10).size == 3

    def test_同一种子可复现(self):
        from svc import DeterministicRNG
        a = pos_challenge(50, 5, DeterministicRNG(b"s"))
        b = pos_challenge(50, 5, DeterministicRNG(b"s"))
        assert a.indices == b.indices

    @pytest.mark.parametrize("n,k", [(0, 4), (4, 0), (-1, 4), (4, -1)])
    def test_非法输入(self, n, k):
        with pytest.raises(ValueError):
            pos_challenge(n, k)


# ---------------------------------------------------------------------------
# 正常路径
# ---------------------------------------------------------------------------

class TestHonest:
    def test_收齐后验证通过(self, deployed, session):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        proofs = [n.pos_prove(r) for n in deployed["nodes"]]
        b, agg = pos_aggregate_all(deployed["crs_n"], r, proofs)
        assert b and agg.Q == r.indices
        assert deployed["client"].pos_ver(r, agg).ok

    def test_各节点只答自己那段(self, deployed):
        r = deployed["client"].pos_challenge(16)
        proofs = [n.pos_prove(r) for n in deployed["nodes"]]
        for nd, p in zip(deployed["nodes"], proofs):
            assert set(p.Q) <= set(nd.I)
            assert set(p.Q) <= set(r.indices)
        # 各段拼起来正好是 r
        assert sorted(i for p in proofs for i in p.Q) == list(r.indices)

    def test_挑战没打到的节点返回空证明(self, deployed):
        # 只挑战 node-0 持有的下标
        r = Challenge(indices=tuple(deployed["nodes"][0].I[:3]), n=deployed["delta"].n)
        empty = deployed["nodes"][1].pos_prove(r)
        assert empty.Q == ()

    def test_聚合顺序无关(self, deployed):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        proofs = [n.pos_prove(r) for n in deployed["nodes"]]
        import itertools

        seen = set()
        for perm in itertools.permutations(proofs):
            b, agg = pos_aggregate_all(deployed["crs_n"], r, perm)
            assert b
            seen.add(agg.pi_Q.S_I)
        # 无论以什么顺序合并，最终证明都是同一个
        assert len(seen) == 1

    def test_子集包含时走捷径(self, deployed, session):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        proofs = [n.pos_prove(r) for n in deployed["nodes"]]
        b, agg = pos_aggregate_all(deployed["crs_n"], r, proofs)
        # 再和一份更小的证明合并：应当原样返回已收齐的那份
        smaller = PoSProof(Q=agg.Q[:2], F_Q=agg.F_Q[:2], pi_Q=agg.pi_Q)
        b2, agg2 = pos_aggregate(deployed["crs_n"], r, agg, smaller)
        assert b2 and agg2.pi_Q.S_I == agg.pi_Q.S_I


# ---------------------------------------------------------------------------
# 攻击
# ---------------------------------------------------------------------------

class TestAttacks:
    def test_只给部分节点收不齐(self, deployed):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        proofs = [n.pos_prove(r) for n in deployed["nodes"]]
        b, agg = pos_aggregate_all(deployed["crs_n"], r, proofs[:2])
        rep = deployed["client"].pos_ver(r, agg)
        assert not b and not rep.ok and rep.code.name == "BAD_SHAPE"
        assert "挑战未收齐" in rep.message

    def test_完全不应答(self, deployed, session):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        report = pos_ver(deployed["client"], r, PoSProof(Q=(), F_Q=(), pi_Q=Opening(0, 0, ())))
        assert not report.ok and report.code.name == "BAD_SHAPE"

    @pytest.mark.parametrize("forge", [False, True])
    def test_篡改或伪造在聚合阶段被拒(self, deployed, session, forge):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        evil = _tampered(deployed["nodes"][0], session, forge_proof=forge)
        proofs = [evil.pos_prove(r)] + [n.pos_prove(r) for n in deployed["nodes"][1:]]
        with pytest.raises(ValueError):
            pos_aggregate_all(deployed["crs_n"], r, proofs)

    @pytest.mark.parametrize("forge", [False, True])
    def test_宽容模式下报未收齐(self, deployed, session, forge):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        evil = _tampered(deployed["nodes"][0], session, forge_proof=forge)
        proofs = [evil.pos_prove(r)] + [n.pos_prove(r) for n in deployed["nodes"][1:]]
        b, agg = pos_aggregate_all(deployed["crs_n"], r, proofs, strict=False)
        assert not b
        assert not deployed["client"].pos_ver(r, agg).ok

    def test_多答下标不被接受(self, deployed):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        proofs = [n.pos_prove(r) for n in deployed["nodes"]]
        b, agg = pos_aggregate_all(deployed["crs_n"], r, proofs)
        # 手改 Q 多塞一个下标
        extra = tuple(sorted(set(agg.Q) | {next(i for i in range(N_BLOCKS) if i not in agg.Q)}))
        bad = PoSProof(Q=extra, F_Q=agg.F_Q + (0,), pi_Q=agg.pi_Q)
        rep = deployed["client"].pos_ver(r, bad)
        assert not rep.ok and "挑战未收齐" in rep.message

    def test_没有任何份额时报错(self, deployed):
        r = deployed["client"].pos_challenge(LAMBDA_POS)
        with pytest.raises(ValueError):
            pos_aggregate_all(deployed["crs_n"], r, [PoSProof(Q=(), F_Q=(), pi_Q=Opening(0, 0, ()))])


# ---------------------------------------------------------------------------
# 并行 PoS
# ---------------------------------------------------------------------------

class TestParallel:
    @pytest.fixture(scope="class")
    def two_files(self, session):
        groups = [list(range(i, N_BLOCKS, 4)) for i in range(4)]
        out = []
        for tag in (b"A", b"B"):
            delta, crs_n, values, _ = session.commit_bytes(
                bytes([tag[0]]) * (N_BLOCKS * BLOCK_BYTES), BLOCK_BYTES
            )
            out.append(
                {
                    "delta": delta, "crs_n": crs_n, "values": values,
                    "nodes": session.distribute(delta, values, groups),
                    "client": session.make_client(delta),
                }
            )
        return out

    def test_一个挑战验两个文件(self, two_files):
        r = parallel_pos_challenge(N_BLOCKS, 12)
        items = []
        for f in two_files:
            _, agg = pos_aggregate_all(
                f["crs_n"], r, [n.pos_prove(r) for n in f["nodes"]]
            )
            items.append((f["client"], agg))
        results = parallel_pos_verify(items, r)
        assert [rep.ok for _, rep in results] == [True, True]

    def test_两个文件的摘要确实不同(self, two_files):
        assert two_files[0]["delta"].C != two_files[1]["delta"].C

    def test_破坏其中一个不影响另一个的判定(self, two_files, session):
        r = parallel_pos_challenge(N_BLOCKS, 12)
        good, bad_f = two_files
        _, good_agg = pos_aggregate_all(
            good["crs_n"], r, [n.pos_prove(r) for n in good["nodes"]]
        )
        evil = _tampered(bad_f["nodes"][0], session)
        _, bad_agg = pos_aggregate_all(
            bad_f["crs_n"], r,
            [evil.pos_prove(r)] + [n.pos_prove(r) for n in bad_f["nodes"][1:]],
            strict=False,
        )
        results = parallel_pos_verify([(good["client"], good_agg),
                                       (bad_f["client"], bad_agg)], r)
        assert results[0][1].ok is True
        assert results[1][1].ok is False
