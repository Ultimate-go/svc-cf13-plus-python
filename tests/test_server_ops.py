"""``server.app`` 各步接口的行为测试。

覆盖两条**只在 op/HTTP 层**才暴露的问题（审计【1】【17】）：

* 【1】``op_verify`` 必须用服务器**实际返回**的内容去验，而不是本地真值 ——
  否则「验证通过」与节点返回了什么无关；
* 【17】``op_setup`` 的参数要有上界，越界直接报错而不是把后端拖很久。
"""

from __future__ import annotations

import pytest

from server import app as srv


@pytest.fixture
def small_session():
    """一个便宜可用的会话（256 位模数，4 字节一块），用完清状态。"""
    srv.op_setup({"n_max": 16, "block_bytes": 4, "modulus_bits": 256})
    yield
    srv.STATE.reset()


class TestSetup参数上界:
    def test_越界参数被拒绝(self):
        bad = [
            {"n_max": 0},
            {"n_max": srv.N_MAX_CAP + 1},
            {"block_bytes": 0},
            {"block_bytes": srv.BLOCK_BYTES_MAX + 1},
            {"modulus_bits": 32},                      # 低于 svc 层下限
            {"modulus_bits": srv.MODULUS_BITS_MAX + 1},
        ]
        for payload in bad:
            with pytest.raises(ValueError):
                srv.op_setup(payload)
        # 被拒的调用不应改动会话状态
        assert srv.STATE.session is None

    def test_边界内参数可用(self, small_session):
        assert srv.STATE.session is not None
        assert srv.STATE.crs_n is None      # 还没 commit


class Test验证用返回内容:
    def test_诚实流程验证通过(self, small_session):
        srv.op_commit({"text": "abcdefghijklmnop"})
        srv.op_distribute({"nodes": 2})
        srv.op_retrieve({"indices": [0]})
        srv.op_aggregate({})
        assert srv.op_verify({})["ok"] is True

    def test_内容被换而证据诚实时验证失败(self, small_session):
        """审计【1】的回归点：这是修之前会被放过的那条。

        节点把取回那块的内容改掉、**证据不动**；检索/聚合照常。
        用「本地真值」验 → 通过（旧行为的 bug）；
        用「服务器实际返回的内容」验 → BAD_LAMBDA。
        """
        srv.op_commit({"text": "abcdefghijklmnop"})
        srv.op_distribute({"nodes": 2})
        Q = [srv.STATE.nodes[0].I[0]]

        # 把 node-0 换成「内容被改、证据诚实」的版本
        evil = srv._tamper_node(srv.STATE.nodes[0], Q[0])
        srv.STATE.nodes = [evil, *srv.STATE.nodes[1:]]

        srv.op_retrieve({"indices": Q})
        srv.op_aggregate({})
        rep = srv.op_verify({})
        assert rep["ok"] is False
        assert rep["code"] == "BAD_LAMBDA"
