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
:mod:`vds.updates`             §8.2 的两段式更新（``PushUpdate``/``ApplyUpdate``）
:mod:`vds.pos`                 附录 D.1 的存储证明（PoR / PDP）
:mod:`vds.vds`                 :class:`~vds.vds.VDSSession`，组装全流程
:mod:`vds.vds1`                §8.1 的 ``VDS1``（含 ``CreateFrom``/``GetCreate``）
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

已实现的范围
------------
* §7 / §8.2 的全部接口；
* §8.2 的三种文件更新（``mod`` / ``add`` / ``del``）走**两段式**：
  :func:`push_update` 产出 :math:`\\Upsilon_\\Delta`，:func:`apply_update`
  先校验它再应用 —— 后者**不需要改动后的内容**；
* 附录 D.1 的存储证明（PoR / PDP）见 :mod:`vds.pos`；
* §8.1 的 ``VDS1`` 见 :mod:`vds.vds1`，包括 ``StrgNode.CreateFrom`` /
  ``ClntNode.GetCreate``（从一个已存文件派生新文件，客户端只需一个
  常数大小的 ``PoKSubV'`` 证明）。它建立在 §5.1 阴阳方案 + §6 的
  知识论证之上，是**另一套**方案，与 :mod:`vds.vds` 的 ``VDS2`` 并列。

两套 VDS 怎么选
---------------
``VDS2``（本模块）承诺与打开各**一个**群元素，但**没有**派生新文件的能力。
``VDS1``（:mod:`vds.vds1`）各**两个**群元素，换来 ``CreateFrom`` /
``GetCreate``，以及不需要 ``VC.Specialize``。论文 §8.3 有对比。
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
    AppliedUpdate,
    PushedUpdate,
    UpdateRecord,
    apply_update,
    push_update,
    update_append,
    update_modify,
    update_truncate,
)
from .pos import (
    Challenge,
    PoSProof,
    parallel_pos_challenge,
    parallel_pos_verify,
    pos_aggregate,
    pos_aggregate_all,
    pos_challenge,
    pos_prove,
    pos_ver,
)
from .vds import VDSSession
from .vds1 import (
    AppliedUpdate1,
    ClientNode1,
    CreateWitness,
    Digest1,
    LocalView1,
    PushedUpdate1,
    StorageNode1,
    UpdateOp1,
    VDS1Session,
    agg_prime,
    com_prime,
    disagg_prime,
    is_prefix,
    poksubv_prime_prove,
    poksubv_prime_verify,
    ver_prime,
)

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
    "PushedUpdate",
    "AppliedUpdate",
    "push_update",
    "apply_update",
    "update_modify",
    "update_append",
    "update_truncate",
    # 附录 D.1 存储证明
    "Challenge",
    "PoSProof",
    "pos_challenge",
    "pos_prove",
    "pos_aggregate",
    "pos_aggregate_all",
    "pos_ver",
    "parallel_pos_challenge",
    "parallel_pos_verify",
    "split_bytes",
    "join_blocks",
    "blocks_for_length",
    "l_for_block_bytes",
    # §8.1 的 VDS1
    "VDS1Session",
    "Digest1",
    "LocalView1",
    "StorageNode1",
    "ClientNode1",
    "CreateWitness",
    "UpdateOp1",
    "PushedUpdate1",
    "AppliedUpdate1",
    "com_prime",
    "ver_prime",
    "disagg_prime",
    "agg_prime",
    "is_prefix",
    "poksubv_prime_prove",
    "poksubv_prime_verify",
]
