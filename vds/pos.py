<<<<<<< HEAD
"""附录 D.1 的存储证明（Proof of Retrievability）。

主流程（检索→聚合→验证）回答的是「你给我的这几块对不对」。
PoR 回答的是另一个问题：**在不下载任何内容的前提下，确认网络确实还存着文件**。
用于防「节点收了钱却偷偷把数据丢掉」。

论文 D.1 的结论是这条构造对**任意** VDS 都成立，所以它直接架在 §8.2 之上，
四个算法（Fig. D.1）::

    ClntNode.PoS-Challenge(n) → r
        抽 λpos 个 [n] 里的下标，r = {r_1, ..., r_λpos}

    StrgNode.PoS-Prove(δ, n, st, I, FI, r) → π_r
        Q := I ∩ r
        (F_Q, π_Q) ← StrgNode.Retrieve(δ, n, st, I, FI, Q)
        return π_r := (Q, F_Q, π_Q)

    StrgNode.PoS-Aggregate(δ, r, π_{r,1}, π_{r,2}) → (b, π_r)
        若某个 Q_i = r：b := 1，π_r := π_{r,i}
        否则 (Q, F_Q) := (Q_1, F_Q1) ∪ (Q_2, F_Q2)
             π_Q ← AggregateCertificates(δ, (Q_1,F_Q1,π_Q1), (Q_2,F_Q2,π_Q2))
             b := (Q = r)，π_r := (Q, F_Q, π_Q)

    ClntNode.PoS-Ver(δ, r, π_r) → b
        解析 π_r := (Q, F_Q, π_Q)
        return (Q = r) ∧ ClntNode.VerRetrieve(δ, Q, F_Q, π_Q)

要点
----
* **完整性判据是 `Q = r`**，不是某一份证明「看起来对」。挑战点名了 λpos 个下标，
  只有全部拿齐，`b` 才为 1；聚合过程可以任意顺序、任意次数。
* 每个节点只答自己负责的那部分（`Q = I ∩ r`），谁也不需要看别的节点
  —— 这满足论文说的「证明分布式生成、且与参与节点数无关地保持紧凑」。
* 最后仍是**一个**常数大小证明，验证一次。

与论文的一处差异
----------------
论文的并行 PDP 提到「验证一个 PDP 要花 O(λpos) 去算 :math:`U_r = g^{u_r}`，
`:math:`u_r = \\prod_{i \\in r} e_i`，并行时可摊薄」。那是 **§5.1** 的性质：
它的验证式里出现了 :math:`U_r`。§5.2 的验证走 :func:`svc.verify` 的
``add_back`` 迭代，:math:`U` 直接取自摘要，**不需要**算 :math:`e_r`。
所以本模块的并行版摊薄的是「协议轮次」而非「群元素计算」，如实记录。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Sequence

from svc import (
    CRSn,
    DeterministicRNG,
    Opening,
    VerifyReport,
    agg_many_to_one,
    verify as svc_verify,
)
from svc.types import as_index_set

if TYPE_CHECKING:  # pragma: no cover
    from .client_node import ClientNode
    from .digest import Digest
    from .storage_node import StorageNode

__all__ = [
    "Challenge",
    "PoSProof",
    "pos_challenge",
    "pos_prove",
    "pos_aggregate",
    "pos_aggregate_all",
    "pos_ver",
    "parallel_pos_challenge",
    "parallel_pos_verify",
]

DEFAULT_LAMBDA_POS = 8

#: ``Q`` 为空时用的占位证明体，内容不参与任何运算
EMPTY_OPENING = Opening(S_I=0, Lambda_I=0, I=())


@dataclass(frozen=True)
class Challenge:
    """``r`` —— 一次存储证明挑战。

    :param indices: 被点名的下标集合
    :param n: 生成挑战时的文件长度
    """

    indices: tuple[int, ...]
    n: int

    @property
    def size(self) -> int:
        return len(self.indices)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"Challenge(|r|={self.size}, n={self.n})"


@dataclass(frozen=True)
class PoSProof:
    """``π_r := (Q, F_Q, π_Q)``。"""

    Q: tuple[int, ...]
    F_Q: tuple[int, ...]
    pi_Q: Opening

    def is_complete(self, challenge: Challenge) -> bool:
        return self.Q == challenge.indices

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"PoSProof(|Q|={len(self.Q)}, complete={self.Q})"


def pos_challenge(
    n: int,
    lambda_pos: int = DEFAULT_LAMBDA_POS,
    rng=None,
) -> Challenge:
    """``ClntNode.PoS-Challenge(n)`` —— 生成挑战。

    :param lambda_pos: 挑战的下标个数，论文记作 :math:`\\lambda_{pos}`。
                       被丢弃的数据比例必须小于 :math:`1/\\lambda_{pos}`
                       才可能答对（论文 Theorem D.2 里 :math:`\\mu^{\\lambda_{pos}}` 那一项）。
    :param rng: 随机源；``None`` 时每次调用结果不同

    论文写 ``r_1, ..., r_λpos ←$ [n]``（可重复），本实现**不放回抽样**，
    这样 :math:`|r|` 恒等于 ``lambda_pos``，覆盖度更可预测；``n < lambda_pos``
    时取满 ``n``。
    """
    if n <= 0:
        raise ValueError("文件长度 n 必须为正")
    if lambda_pos <= 0:
        raise ValueError("lambda_pos 必须为正")

    k = min(lambda_pos, n)
    if rng is None:
        rng = DeterministicRNG()

    picked: set[int] = set()
    while len(picked) < k:
        picked.add(rng.randbelow(n))
    return Challenge(indices=as_index_set(picked), n=n)


def pos_prove(node: "StorageNode", challenge: Challenge) -> PoSProof:
    """``StrgNode.PoS-Prove`` —— 节点回答自己负责的那部分挑战。

    ``Q := I ∩ r``，然后用 ``StrgNode.Retrieve`` 同时拿到内容与证明。
    ``Q`` 为空（挑战没打到这个节点）时返回一份空证明，
    聚合阶段会直接跳过它。
    """
    Q = as_index_set(set(node.I) & set(challenge.indices))
    if not Q:
        return PoSProof(Q=(), F_Q=(), pi_Q=EMPTY_OPENING)

    F_Q, pi_Q = node.retrieve(Q)
    return PoSProof(Q=Q, F_Q=F_Q, pi_Q=pi_Q)


def pos_aggregate(
    crs_n: CRSn,
    challenge: Challenge,
    left: PoSProof,
    right: PoSProof,
) -> tuple[bool, PoSProof]:
    """``StrgNode.PoS-Aggregate`` —— 合并两份部分证明。

    :returns: ``(b, π_r)``，``b = 1`` 表示合并结果已经覆盖整个挑战

    合并规则（论文原文的顺序）：

    1. 任一侧已经覆盖 ``r`` 就直接采信那一侧（``b := 1``）；
    2. 一侧的下标集包含于另一侧时丢掉小的那份；
    3. 否则两份**不相交**时走 :func:`svc.agg_many_to_one` 合并；
    4. 部分重叠（互不包含且交集非空）无法直接合并，
       需要先 :func:`svc.disagg` 削掉重叠 —— 抛错而不是静默出错。

    第 2 条保证合并是**单调**的（并集只增不减），
    所以反复合并最终一定能覆盖 ``r``（只要各节点份额加起来确实是 ``r``）。
    """
    if not left.Q:
        return right.is_complete(challenge), right
    if not right.Q:
        return left.is_complete(challenge), left

    if left.is_complete(challenge):
        return True, left
    if right.is_complete(challenge):
        return True, right

    sl, sr = set(left.Q), set(right.Q)
    if sl <= sr:
        return right.is_complete(challenge), right
    if sr <= sl:
        return left.is_complete(challenge), left

    if sl & sr:
        raise ValueError(
            f"两份部分证明在 {sorted(sl & sr)} 上重叠，无法直接合并；"
            f"请先用 svc.disagg 削掉重叠部分"
        )

    merged = agg_many_to_one(
        crs_n,
        [(left.Q, left.F_Q, left.pi_Q), (right.Q, right.F_Q, right.pi_Q)],
    )
    # merged.I 是排序后的并集，值必须按同一顺序重摆；
    # 直接拼接 left.F_Q + right.F_Q 会让「下标 i 的值」错位，
    # 下一次合并时 ShamirTrick 的同源自检就会失败。
    valmap = dict(zip(left.Q, left.F_Q))
    valmap.update(zip(right.Q, right.F_Q))
    proof = PoSProof(
        Q=merged.I,
        F_Q=tuple(valmap[i] for i in merged.I),
        pi_Q=merged,
    )
    return proof.is_complete(challenge), proof


def pos_aggregate_all(
    crs_n: CRSn,
    challenge: Challenge,
    proofs: Sequence[PoSProof],
    *,
    strict: bool = True,
) -> tuple[bool, PoSProof]:
    """把一批部分证明按**给定顺序**依次合并，直到 ``b = 1``。

    论文要求「任意顺序、重复使用 PoS-Aggregate 直到 ``b = 1``」。
    合并是单调的（并集只增不减），所以折叠顺序不影响最终能否覆盖 ``r``。

    :param strict: 某份份额合并不了时是否抛错。
                   默认 ``True``，与 :func:`svc.agg` 一致 ——
                   被篡改的证据会在 ``ShamirTrick`` 的同源自检处失败，
                   于是**连一份可验证的假证明都拼不出来**。
                   传 ``False`` 则跳过合并不了的份额继续尝试，
                   此时 ``b`` 保持 ``False``，由 :func:`pos_ver`
                   报「挑战未收齐」—— 篡改依然被抓住，只是错误信息不同。

    :raises ValueError: ``proofs`` 里没有一份覆盖到挑战下标，
                        或 ``strict=True`` 时出现合并不了的份额。
    """
    live = [p for p in proofs if p.Q]
    if not live:
        raise ValueError("没有任何一份部分证明覆盖到挑战下标")

    acc = live[0]
    if acc.is_complete(challenge):
        return True, acc
    for p in live[1:]:
        try:
            done, acc = pos_aggregate(crs_n, challenge, acc, p)
        except ValueError:
            if strict:
                raise
            continue
        if done:
            return True, acc
    return False, acc


def pos_ver(
    client: "ClientNode",
    challenge: Challenge,
    proof: PoSProof,
) -> VerifyReport:
    """``ClntNode.PoS-Ver`` —— 验证收齐的存储证明。

    判据两道：``Q = r``（收齐了）**且** ``VerRetrieve`` 通过（内容没被换掉）。
    任一条不满足都不接受。
    """
    from svc import VerifyCode

    if not proof.is_complete(challenge):
        missing = sorted(set(challenge.indices) - set(proof.Q))
        extra = sorted(set(proof.Q) - set(challenge.indices))
        detail = []
        if missing:
            detail.append(f"缺少下标 {missing[:8]}" + ("…" if len(missing) > 8 else ""))
        if extra:
            detail.append(f"多出下标 {extra[:8]}" + ("…" if len(extra) > 8 else ""))
        return VerifyReport.fail(
            VerifyCode.BAD_SHAPE, "挑战未收齐：" + "；".join(detail)
        )

    return client.ver_retrieve(list(proof.Q), list(proof.F_Q), proof.pi_Q)


# ---------------------------------------------------------------------------
# 并行版（论文 "Parallel Proof of Storage"）
# ---------------------------------------------------------------------------

def parallel_pos_challenge(
    n: int,
    lambda_pos: int = DEFAULT_LAMBDA_POS,
    rng=None,
) -> Challenge:
    """并行 PoS 的挑战：**只依赖文件长度**，因此一份挑战可同时用于 k 个等长文件。

    见论文 "We extend our PoS notion for VDS to a setting where one can
    simultaneously check storage of k different files of the same length
    with a single challenge."
    """
    return pos_challenge(n, lambda_pos, rng)


def parallel_pos_verify(
    items: Sequence[tuple["ClientNode", PoSProof]],
    challenge: Challenge,
) -> list[tuple["Digest", VerifyReport]]:
    """用同一个挑战一次性验证 k 个文件。

    :param items: ``(客户端, 该文件的部分证明)`` 序列；每个客户端各持自己那份摘要
    :returns: 与 ``items`` 等长的 ``(摘要, 报告)`` 列表

    注意诚实性：论文在并行 PDP 一节说并行可以摊薄 :math:`U_r` 的计算，
    但那是 §5.1 的性质。§5.2 的验证不构造 :math:`U_r`，
    所以这里摊薄的只是**通信轮次与挑战生成**，不是群元素运算。
    """
    out: list[tuple["Digest", VerifyReport]] = []
    for client, proof in items:
        out.append((client.delta, pos_ver(client, challenge, proof)))
    return out
=======
"""附录 D.1 的存储证明（Proof of Retrievability）。

主流程（检索→聚合→验证）回答的是「你给我的这几块对不对」。
PoR 回答的是另一个问题：**在不下载任何内容的前提下，确认网络确实还存着文件**。
用于防「节点收了钱却偷偷把数据丢掉」。

论文 D.1 的结论是这条构造对**任意** VDS 都成立，所以它直接架在 §8.2 之上，
四个算法（Fig. D.1）::

    ClntNode.PoS-Challenge(n) → r
        抽 λpos 个 [n] 里的下标，r = {r_1, ..., r_λpos}

    StrgNode.PoS-Prove(δ, n, st, I, FI, r) → π_r
        Q := I ∩ r
        (F_Q, π_Q) ← StrgNode.Retrieve(δ, n, st, I, FI, Q)
        return π_r := (Q, F_Q, π_Q)

    StrgNode.PoS-Aggregate(δ, r, π_{r,1}, π_{r,2}) → (b, π_r)
        若某个 Q_i = r：b := 1，π_r := π_{r,i}
        否则 (Q, F_Q) := (Q_1, F_Q1) ∪ (Q_2, F_Q2)
             π_Q ← AggregateCertificates(δ, (Q_1,F_Q1,π_Q1), (Q_2,F_Q2,π_Q2))
             b := (Q = r)，π_r := (Q, F_Q, π_Q)

    ClntNode.PoS-Ver(δ, r, π_r) → b
        解析 π_r := (Q, F_Q, π_Q)
        return (Q = r) ∧ ClntNode.VerRetrieve(δ, Q, F_Q, π_Q)

要点
----
* **完整性判据是 `Q = r`**，不是某一份证明「看起来对」。挑战点名了 λpos 个下标，
  只有全部拿齐，`b` 才为 1；聚合过程可以任意顺序、任意次数。
* 每个节点只答自己负责的那部分（`Q = I ∩ r`），谁也不需要看别的节点
  —— 这满足论文说的「证明分布式生成、且与参与节点数无关地保持紧凑」。
* 最后仍是**一个**常数大小证明，验证一次。

与论文的一处差异
----------------
论文的并行 PDP 提到「验证一个 PDP 要花 O(λpos) 去算 :math:`U_r = g^{u_r}`，
`:math:`u_r = \\prod_{i \\in r} e_i`，并行时可摊薄」。那是**双累加器版**的性质：
它的验证式里出现了 :math:`U_r`。本方案的验证走 :func:`svc.verify` 的
``add_back`` 迭代，:math:`U` 直接取自摘要，**不需要**算 :math:`e_r`。
所以本模块的并行版摊薄的是「协议轮次」而非「群元素计算」，如实记录。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Sequence

from svc import (
    CRSn,
    DeterministicRNG,
    Opening,
    VerifyReport,
    agg_many_to_one,
    verify as svc_verify,
)
from svc.types import as_index_set

if TYPE_CHECKING:  # pragma: no cover
    from .client_node import ClientNode
    from .digest import Digest
    from .storage_node import StorageNode

__all__ = [
    "Challenge",
    "PoSProof",
    "pos_challenge",
    "pos_prove",
    "pos_aggregate",
    "pos_aggregate_all",
    "pos_ver",
    "parallel_pos_challenge",
    "parallel_pos_verify",
]

DEFAULT_LAMBDA_POS = 8

#: ``Q`` 为空时用的占位证明体，内容不参与任何运算
EMPTY_OPENING = Opening(S_I=0, Lambda_I=0, I=())


@dataclass(frozen=True)
class Challenge:
    """``r`` —— 一次存储证明挑战。

    :param indices: 被点名的下标集合
    :param n: 生成挑战时的文件长度
    """

    indices: tuple[int, ...]
    n: int

    @property
    def size(self) -> int:
        return len(self.indices)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"Challenge(|r|={self.size}, n={self.n})"


@dataclass(frozen=True)
class PoSProof:
    """``π_r := (Q, F_Q, π_Q)``。"""

    Q: tuple[int, ...]
    F_Q: tuple[int, ...]
    pi_Q: Opening

    def is_complete(self, challenge: Challenge) -> bool:
        return self.Q == challenge.indices

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"PoSProof(|Q|={len(self.Q)}, complete={self.Q})"


def pos_challenge(
    n: int,
    lambda_pos: int = DEFAULT_LAMBDA_POS,
    rng=None,
) -> Challenge:
    """``ClntNode.PoS-Challenge(n)`` —— 生成挑战。

    :param lambda_pos: 挑战的下标个数，论文记作 :math:`\\lambda_{pos}`。
                       被丢弃的数据比例必须小于 :math:`1/\\lambda_{pos}`
                       才可能答对（论文 Theorem D.2 里 :math:`\\mu^{\\lambda_{pos}}` 那一项）。
    :param rng: 随机源；``None`` 时每次调用结果不同

    论文写 ``r_1, ..., r_λpos ←$ [n]``（可重复），本实现**不放回抽样**，
    这样 :math:`|r|` 恒等于 ``lambda_pos``，覆盖度更可预测；``n < lambda_pos``
    时取满 ``n``。
    """
    if n <= 0:
        raise ValueError("文件长度 n 必须为正")
    if lambda_pos <= 0:
        raise ValueError("lambda_pos 必须为正")

    k = min(lambda_pos, n)
    if rng is None:
        rng = DeterministicRNG()

    picked: set[int] = set()
    while len(picked) < k:
        picked.add(rng.randbelow(n))
    return Challenge(indices=as_index_set(picked), n=n)


def pos_prove(node: "StorageNode", challenge: Challenge) -> PoSProof:
    """``StrgNode.PoS-Prove`` —— 节点回答自己负责的那部分挑战。

    ``Q := I ∩ r``，然后用 ``StrgNode.Retrieve`` 同时拿到内容与证明。
    ``Q`` 为空（挑战没打到这个节点）时返回一份空证明，
    聚合阶段会直接跳过它。
    """
    Q = as_index_set(set(node.I) & set(challenge.indices))
    if not Q:
        return PoSProof(Q=(), F_Q=(), pi_Q=EMPTY_OPENING)

    F_Q, pi_Q = node.retrieve(Q)
    return PoSProof(Q=Q, F_Q=F_Q, pi_Q=pi_Q)


def pos_aggregate(
    crs_n: CRSn,
    challenge: Challenge,
    left: PoSProof,
    right: PoSProof,
) -> tuple[bool, PoSProof]:
    """``StrgNode.PoS-Aggregate`` —— 合并两份部分证明。

    :returns: ``(b, π_r)``，``b = 1`` 表示合并结果已经覆盖整个挑战

    合并规则（论文原文的顺序）：

    1. 任一侧已经覆盖 ``r`` 就直接采信那一侧（``b := 1``）；
    2. 一侧的下标集包含于另一侧时丢掉小的那份；
    3. 否则两份**不相交**时走 :func:`svc.agg_many_to_one` 合并；
    4. 部分重叠（互不包含且交集非空）无法直接合并，
       需要先 :func:`svc.disagg` 削掉重叠 —— 抛错而不是静默出错。

    第 2 条保证合并是**单调**的（并集只增不减），
    所以反复合并最终一定能覆盖 ``r``（只要各节点份额加起来确实是 ``r``）。
    """
    if not left.Q:
        return right.is_complete(challenge), right
    if not right.Q:
        return left.is_complete(challenge), left

    if left.is_complete(challenge):
        return True, left
    if right.is_complete(challenge):
        return True, right

    sl, sr = set(left.Q), set(right.Q)
    if sl <= sr:
        return right.is_complete(challenge), right
    if sr <= sl:
        return left.is_complete(challenge), left

    if sl & sr:
        raise ValueError(
            f"两份部分证明在 {sorted(sl & sr)} 上重叠，无法直接合并；"
            f"请先用 svc.disagg 削掉重叠部分"
        )

    merged = agg_many_to_one(
        crs_n,
        [(left.Q, left.F_Q, left.pi_Q), (right.Q, right.F_Q, right.pi_Q)],
    )
    # merged.I 是排序后的并集，值必须按同一顺序重摆；
    # 直接拼接 left.F_Q + right.F_Q 会让「下标 i 的值」错位，
    # 下一次合并时 ShamirTrick 的同源自检就会失败。
    valmap = dict(zip(left.Q, left.F_Q))
    valmap.update(zip(right.Q, right.F_Q))
    proof = PoSProof(
        Q=merged.I,
        F_Q=tuple(valmap[i] for i in merged.I),
        pi_Q=merged,
    )
    return proof.is_complete(challenge), proof


def pos_aggregate_all(
    crs_n: CRSn,
    challenge: Challenge,
    proofs: Sequence[PoSProof],
    *,
    strict: bool = True,
) -> tuple[bool, PoSProof]:
    """把一批部分证明按**给定顺序**依次合并，直到 ``b = 1``。

    论文要求「任意顺序、重复使用 PoS-Aggregate 直到 ``b = 1``」。
    合并是单调的（并集只增不减），所以折叠顺序不影响最终能否覆盖 ``r``。

    :param strict: 某份份额合并不了时是否抛错。
                   默认 ``True``，与 :func:`svc.agg` 一致 ——
                   被篡改的证据会在 ``ShamirTrick`` 的同源自检处失败，
                   于是**连一份可验证的假证明都拼不出来**。
                   传 ``False`` 则跳过合并不了的份额继续尝试，
                   此时 ``b`` 保持 ``False``，由 :func:`pos_ver`
                   报「挑战未收齐」—— 篡改依然被抓住，只是错误信息不同。

    :raises ValueError: ``proofs`` 里没有一份覆盖到挑战下标，
                        或 ``strict=True`` 时出现合并不了的份额。
    """
    live = [p for p in proofs if p.Q]
    if not live:
        raise ValueError("没有任何一份部分证明覆盖到挑战下标")

    acc = live[0]
    if acc.is_complete(challenge):
        return True, acc
    for p in live[1:]:
        try:
            done, acc = pos_aggregate(crs_n, challenge, acc, p)
        except ValueError:
            if strict:
                raise
            continue
        if done:
            return True, acc
    return False, acc


def pos_ver(
    client: "ClientNode",
    challenge: Challenge,
    proof: PoSProof,
) -> VerifyReport:
    """``ClntNode.PoS-Ver`` —— 验证收齐的存储证明。

    判据两道：``Q = r``（收齐了）**且** ``VerRetrieve`` 通过（内容没被换掉）。
    任一条不满足都不接受。
    """
    from svc import VerifyCode

    if not proof.is_complete(challenge):
        missing = sorted(set(challenge.indices) - set(proof.Q))
        extra = sorted(set(proof.Q) - set(challenge.indices))
        detail = []
        if missing:
            detail.append(f"缺少下标 {missing[:8]}" + ("…" if len(missing) > 8 else ""))
        if extra:
            detail.append(f"多出下标 {extra[:8]}" + ("…" if len(extra) > 8 else ""))
        return VerifyReport.fail(
            VerifyCode.BAD_SHAPE, "挑战未收齐：" + "；".join(detail)
        )

    return client.ver_retrieve(list(proof.Q), list(proof.F_Q), proof.pi_Q)


# ---------------------------------------------------------------------------
# 并行版（论文 "Parallel Proof of Storage"）
# ---------------------------------------------------------------------------

def parallel_pos_challenge(
    n: int,
    lambda_pos: int = DEFAULT_LAMBDA_POS,
    rng=None,
) -> Challenge:
    """并行 PoS 的挑战：**只依赖文件长度**，因此一份挑战可同时用于 k 个等长文件。

    见论文 "We extend our PoS notion for VDS to a setting where one can
    simultaneously check storage of k different files of the same length
    with a single challenge."
    """
    return pos_challenge(n, lambda_pos, rng)


def parallel_pos_verify(
    items: Sequence[tuple["ClientNode", PoSProof]],
    challenge: Challenge,
) -> list[tuple["Digest", VerifyReport]]:
    """用同一个挑战一次性验证 k 个文件。

    :param items: ``(客户端, 该文件的部分证明)`` 序列；每个客户端各持自己那份摘要
    :returns: 与 ``items`` 等长的 ``(摘要, 报告)`` 列表

    注意诚实性：论文在并行 PDP 一节说并行可以摊薄 :math:`U_r` 的计算，
    但那是双累加器版的性质。本方案的验证不构造 :math:`U_r`，
    所以这里摊薄的只是**通信轮次与挑战生成**，不是群元素运算。
    """
    out: list[tuple["Digest", VerifyReport]] = []
    for client, proof in items:
        out.append((client.delta, pos_ver(client, challenge, proof)))
    return out
>>>>>>> main
