"""VDS 应用层 —— 论文 §8.2 的 ``VDS2``。

把 :mod:`svc` 里的第二个 SVC 套上「一个客户端 + 多个互不信任的存储节点」
的框架，实现可验证分布式存储（Verifiable Decentralized Storage）。

这个包解决什么问题
------------------
一个文件被切成若干块、分散存在多台服务器上。任何人想要其中若干部分时，
服务器把内容连同**证据**一起返回。关键要求有三个：

1. **证据是常数的** —— 不论取多少块、文件多大，证据永远是两个群元素；
2. **证据可以聚合** —— 从多台服务器拿到的多份证据能合成**一个**；
3. **验证者是零信任的** —— 客户端只保存一个常数量摘要，
   凭它就能验证聚合后的那一个证据，确认**所有**取回的块都没被动过。

模块导航
--------
============================  ==========================================
模块                           内容
============================  ==========================================
:mod:`vds.digest`              摘要 :math:`\\delta` 与本地视图
:mod:`vds.encoding`            文件 ↔ 块 的编码
:mod:`vds.storage_node`        ``StrgNode.*``
:mod:`vds.client_node`         ``ClntNode.*``
:mod:`vds.vds`                 :class:`~vds.vds.VDSSession`，组装全流程
============================  ==========================================

最小用法
--------
::

    from vds import VDSSession

    s = VDSSession(n_max=16, l=128, lambda_bits=128)
    delta, crs_n, values, nbytes = s.commit_bytes(b"hello world", block_bytes=16)

    nodes = s.distribute(delta, values, [[0, 1, 2, 3], [4, 5, 6, 7],
                                         [8, 9, 10, 11], [12, 13, 14, 15]])

    client = s.make_client(delta)
    F_Q, certs, used = s.retrieve_from(nodes, [1, 2, 9, 10])
    Q, values_out, report = client.retrieve_and_verify(certs)
    assert report.ok

未实现的部分
------------
``StrgNode.CreateFrom`` 与 ``ClntNode.GetCreate`` **未实现**，
它们依赖论文 §6 的独立协议 ``PoKSubV``（子向量知识论证）。
主流程不受影响。详见 ``docs/与论文对照.md``。
"""

from __future__ import annotations

from .client_node import Certificate, ClientNode
from .digest import Digest, LocalView
from .encoding import (
    blocks_for_length,
    join_blocks,
    l_for_block_bytes,
    split_bytes,
)
from .storage_node import StorageNode, UpdateDelta, UpdateWitness
from .updates import (
    UpdateRecord,
    update_append,
    update_modify,
    update_truncate,
)
from .vds import VDSSession

__all__ = [
    "VDSSession",
    "Digest",
    "LocalView",
    "StorageNode",
    "ClientNode",
    "Certificate",
    "UpdateDelta",
    "UpdateWitness",
    "UpdateRecord",
    "update_modify",
    "update_append",
    "update_truncate",
    "split_bytes",
    "join_blocks",
    "blocks_for_length",
    "l_for_block_bytes",
]
