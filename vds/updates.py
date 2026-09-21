"""文件更新 —— 论文 §8.2 的 ``StrgNode.PushUpdate`` / ``ApplyUpdate``。

论文把更新拆成**两段**：

1. ``PushUpdate`` —— 持有改动内容的一方算出新状态与新摘要，
   再产出一个**更新见证** :math:`\\Upsilon_\\Delta`（论文叫「更新密钥」）；
2. ``ApplyUpdate`` —— 收到更新通知的一方（**没有改动后的内容**）
   先用 :math:`\\Upsilon_\\Delta` 校验 ``b ← (S_K^{∏ e_j} = U)``，
   ``b = 1`` 才把新摘要与新状态算出来。

分开的意义在于第 2 段不需要数据：一个存储节点只要拿到 ``δ``、``∆``、:math:`\\Upsilon_\\Delta`
和自己的份额，就能确认「这个更新是合法的」并跟上。这正是 :math:`\\Upsilon_\\Delta`
里只要放**一个群元素** :math:`S_K` 的原因 —— 由它经
:func:`_membership_witnesses` 可推出整批 :math:`S_i`。

三个 op 的公式
--------------
记节点持有 :math:`\\pi_I = d(v \\setminus I) = (S_I, \\Lambda_I)`，
:math:`S_K = g^{e_{[n]}/e_K}`。以下三式都是**从摘要代数独立推导**的，
不是论文正文的逐字转写（原因见文末「与论文的出入」）。

``mod``（只改值，``n`` 不变）::

    C' = C · ∏_{i∈K} S_i^{Δ_i},   Δ_i = F'_i − F_i,   U' = U
    Λ'_I = Λ_I · ∏_{i∈K\\I} (S_I^{1/e_i})^{Δ_i}

:math:`\\Lambda_I` 只含 :math:`j \\notin I` 的值，所以**被改的位置若在 ``I`` 里
则完全不影响** :math:`\\Lambda_I`。修正项里 :math:`S_I^{1/e_i}` 就是
``ShamirTrick(S_I, S_i, e_I, e_i)``（两根同源、且 :math:`i \\notin I` 保证互素）。

``add``（末尾追加，``n' = n + k``）::

    (U', C') = 对 (U, C) 依次 add_back 每个新位置
    S'_I     = S_I^{e_K}
    Λ'_I     = Λ_I^{e_K} · ∏_{j∈K} (S'^{1/e_j}_I)^{v_j}

新位置的成员见证 :math:`S'_j = U^{e_K/e_j}`（:math:`U` 是旧累加器，公开量）。
另外 :math:`\\pi_K^{new} = d_{new}(v \\setminus K) = (U, C)` —— 新位置那个子向量的
证明**就是旧摘要本身**，因为「除 K 之外的其余部分」正是旧文件。

``del``（删末尾 ``k`` 个）::

    δ' = π_K = d(v \\ K),   n' = n − k

``K ⊆ I`` 的节点：:math:`J = I \\setminus K`，
:math:`(S_J, \\Lambda_J)` **一个字节都不用改** ——
:math:`S'_J = g^{e_{[n']}/e_J} = g^{e_{[n]}/(e_K \\cdot e_I/e_K)} = S_I`。
``I ∩ K = ∅`` 的节点：新状态就是 :math:`\\text{agg}(\\pi_I, \\pi_K)`。

与论文的出入
------------
论文 §8.2 的 ``PushUpdate`` / ``ApplyUpdate`` 正文里用的是 **§5.1 阴阳方案**
的原语（``Γ/∆``、``PartndPrimeProd``），而摘要却是 §5.2 的形式
:math:`\\delta = ((U, C), n)` —— 该节是从 §8.1 抄过来的，记号没改。

因此本模块的做法是：**按摘要代数重新推导**，再用独立的 :func:`svc.verify`
验证每一步（只要更新后所有节点的本地视图仍合法、检索仍能通过验证，公式就是对的）。
两处已知的论文笔误在代码里就地标注（``add`` 的校验端、``C'`` 的形态）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from svc import (
    Opening,
    add_back,
    agg,
    batch_root_factor_any,
    disagg,
    e_of,
    shamir_trick,
)
from svc.types import as_index_set, fingerprint

from .digest import Digest, LocalView
from .storage_node import StorageNode, UpdateDelta, UpdateWitness

__all__ = [
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
]


# ---------------------------------------------------------------------------
# 返回结构
# ---------------------------------------------------------------------------

@dataclass
class PushedUpdate:
    """``PushUpdate`` 的输出 ``(δ′, n′, st′, J, F′_J, Υ∆)``。"""

    delta: Digest
    node: StorageNode
    witness: UpdateWitness


@dataclass
class AppliedUpdate:
    """``ApplyUpdate`` 的输出 ``(b, δ′, n′, st′, J, F′_J)``。

    ``ok`` 为假时 :attr:`delta` 与 :attr:`node` 都是 ``None`` ——
    校验没过就什么都不改，这是两段式协议的关键约定。
    """

    ok: bool
    message: str
    delta: Digest | None = None
    node: StorageNode | None = None


@dataclass
class UpdateRecord:
    """一次系统级更新的完整记录，供演示与审计使用。"""

    op: str
    K: tuple[int, ...]
    F_new: tuple[int, ...]
    new_delta: Digest
    witness: UpdateWitness | None = None
    new_nodes: list = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    node_changes: list[str] = field(default_factory=list)
    witness_ok: bool = False

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"UpdateRecord(op={self.op!r}, K={list(self.K)}, → {self.new_delta!r})"


# ---------------------------------------------------------------------------
# 内部工具
# ---------------------------------------------------------------------------

def _membership_witnesses(S_K: int, K: Sequence[int], primegen, N: int) -> dict[int, int]:
    """由聚合成一体的 :math:`S_K` 反推 :math:`K` 里每个位置的成员见证 :math:`S_i`。

    .. code-block:: text

        S_K^(e_K/e_i) = (g^(e_[n]/e_K))^(e_K/e_i) = g^(e_[n]/e_i) = S_i

    一个群元素换成整批见证，这就是 :math:`\\Upsilon_\\Delta` 只放 ``S_K`` 的理由。
    """
    es = [primegen.get(i) for i in K]
    return dict(zip(K, batch_root_factor_any(S_K, es, N)))


def _S_K(session, delta: Digest, node: StorageNode | None, K: Sequence[int]) -> int:
    """求 :math:`S_K = g^{e_{[n]}/e_K}`。

    ``K ⊆ node.I`` 时从该节点**拆**出来（:math:`O(\\ell|I \\setminus K|)`）；
    否则退回一次直接模幂（指数约 ``n(ℓ+1)`` 位）。两条路结果相同。
    """
    if node is not None and set(K) <= set(node.I):
        return disagg(
            session.crs_n_for(delta), list(node.I), list(node.FI), node.st, K
        ).S_I
    crs_n = session.crs_n_for(delta)
    return pow(
        session.crs.g,
        crs_n.e_all // e_of(session.crs.primegen, K),
        session.crs.N,
    )


def _holder_of(nodes: Sequence[StorageNode], K: Sequence[int]) -> StorageNode:
    need = set(K)
    for nd in nodes:
        if need <= set(nd.I):
            return nd
    raise ValueError(
        f"没有任何节点完整持有下标 {sorted(need)}；"
        f"请先让节点用 add_storage 合并出所需区间"
    )


def _old_values(nodes: Sequence[StorageNode], K) -> dict[int, int]:
    """从各节点查 ``K`` 里每个下标的旧值（``K`` 可以横跨多个节点）。"""
    out: dict[int, int] = {}
    for i in K:
        for nd in nodes:
            try:
                out[i] = nd.view.value_of(i)
                break
            except KeyError:
                continue
        else:
            raise ValueError(f"没有任何节点持有下标 {i}")
    return out


def _rebuild(
    session,
    delta: Digest,
    nd: StorageNode,
    st: Opening,
    I: Sequence[int] | None = None,
    FI: Sequence[int] | None = None,
) -> StorageNode:
    """用新的 ``st`` / ``I`` / ``FI`` 重建一个节点。

    ``I`` 与 ``FI`` 必须一起给：``verify`` 会检查证明里的下标与视图一致，
    改了下标集合却留着旧值一定会挂。
    """
    return StorageNode(
        nd.node_id,
        session,
        LocalView(
            delta=delta,
            st=st,
            I=as_index_set(nd.I if I is None else I),
            FI=tuple(nd.FI if FI is None else FI),
        ),
    )


# ---------------------------------------------------------------------------
# PushUpdate —— 产出方
# ---------------------------------------------------------------------------

def push_update(
    session,
    delta: Digest,
    node: StorageNode,
    op_delta: UpdateDelta,
    old_values: dict[int, int] | None = None,
) -> PushedUpdate:
    """``StrgNode.PushUpdate(δ, n, st, I, FI, op, ∆) → (δ′, n′, st′, J, F′_J, Υ∆)``。

    :param node: 发起更新的节点。它的份额会被更新，
                 但它**不必**持有整个 ``K``（``S_K`` 会按需退回直接模幂）。
    :param old_values: ``K`` 上的旧值。``mod`` / ``del`` 需要它来算差值或新摘要；
                       ``None`` 时从 ``node`` 读（读不到就报错）。
    """
    op = op_delta.op
    if op == "mod":
        return _push_mod(session, delta, node, op_delta, old_values)
    if op == "add":
        return _push_add(session, delta, node, op_delta)
    if op == "del":
        return _push_del(session, delta, node, op_delta, old_values)
    raise ValueError(f"未知的 op {op!r}（只支持 mod / add / del）")


def _push_mod(session, delta, node, op_delta: UpdateDelta, old_values) -> PushedUpdate:
    K, F_new = op_delta.K, op_delta.F_new
    if not K:
        raise ValueError("K 不能为空")
    if len(K) != len(F_new):
        raise ValueError("K 与 F_new 长度必须一致")
    n = delta.n
    if K[-1] >= n:
        raise ValueError(f"下标 {K[-1]} 越界（当前 n = {n}）")

    primegen, N = session.crs.primegen, session.crs.N
    old = dict(old_values) if old_values is not None else {
        i: node.view.value_of(i) for i in K
    }
    deltas = {i: F_new[j] - old[i] for j, i in enumerate(K)}

    S_K = _S_K(session, delta, node, K)
    S_i = _membership_witnesses(S_K, K, primegen, N)

    C2 = delta.C
    for i in K:
        if deltas[i]:
            C2 = C2 * pow(S_i[i], deltas[i], N) % N
    new_delta = Digest(U=delta.U, C=C2, n=n)

    st_new, I_new, FI_new = _mod_node_state(node, K, F_new, deltas, S_i, primegen, N)
    witness = UpdateWitness(op="mod", K=K, S_K=S_K, F_K=tuple(old[i] for i in K))
    return PushedUpdate(
        new_delta, _rebuild(session, new_delta, node, st_new, I_new, FI_new), witness
    )


def _mod_node_state(node, K, F_new, deltas, S_i, primegen, N):
    """``mod`` 之后某个节点的 ``(st, I, FI)``。

    位置在 ``I`` 内的：只有值要换，证明不动。
    位置在 ``I`` 外的：:math:`\\Lambda_I` 要按差值修正。
    """
    K_set = set(K)
    outside = [i for i in K if i not in set(node.I)]

    if not outside:
        st_new = node.st
    else:
        e_I = e_of(primegen, node.I)
        Lam = node.st.Lambda_I
        for i in outside:
            if not deltas[i]:
                continue
            t = shamir_trick(node.st.S_I, S_i[i], e_I, primegen.get(i), N)
            if t is None:
                raise ValueError(
                    f"无法为下标 {i} 求更新密钥：ShamirTrick 同源自检失败"
                    f"（下标落在 I 里，或素数映射不一致）"
                )
            Lam = Lam * pow(t, deltas[i], N) % N
        st_new = Opening(node.st.S_I, Lam, node.I)

    newmap = {i: F_new[j] for j, i in enumerate(K)}
    FI_new = tuple(newmap.get(i, v) for i, v in zip(node.I, node.FI))
    return st_new, node.I, FI_new


def _push_add(session, delta, node, op_delta: UpdateDelta) -> PushedUpdate:
    F_new = op_delta.F_new
    if not F_new:
        raise ValueError("至少要追加一个位置")
    n, k = delta.n, len(F_new)
    if n + k > session.n_max:
        raise ValueError(
            f"追加后长度 {n + k} 超过会话上限 n_max = {session.n_max}；"
            f"隐藏阶群的可用位置在 Bootstrap 阶段就定死了"
        )

    primegen, N = session.crs.primegen, session.crs.N
    K = tuple(range(n, n + k))
    e_K = e_of(primegen, K)

    # 新摘要：对 (U, C) 顺序 add_back
    S_cur, Lam_cur = delta.U, delta.C
    for j, v in zip(K, F_new):
        S_cur, Lam_cur = add_back(S_cur, Lam_cur, primegen.get(j), v, N)
    new_delta = Digest(U=S_cur, C=Lam_cur, n=n + k)

    # 新位置在**旧**累加器下的成员见证
    S_j = {j: pow(delta.U, e_K // primegen.get(j), N) for j in K}

    st_new, I_new, FI_new = _add_node_state(node, K, F_new, e_K, S_j, primegen, N)
    # add 的 Υ∆ 就是旧的 U 本身：S_K^{e_K} = U^{e_K} = U′
    witness = UpdateWitness(op="add", K=K, S_K=delta.U, F_K=tuple(F_new))
    return PushedUpdate(
        new_delta, _rebuild(session, new_delta, node, st_new, I_new, FI_new), witness
    )


def _add_node_state(node, K, F_new, e_K, S_j, primegen, N):
    """``add`` 之后某个节点的 ``(st, I, FI)``。

    ``K`` 是末尾新位置，通常不属于任何老节点；此时 ``I`` 不变，
    但 :math:`S_I` 与 :math:`\\Lambda_I` 都要抬 ``e_K`` 次方
    （因为 :math:`e_{[n']} = e_{[n]} \\cdot e_K`）。
    """
    S2 = pow(node.st.S_I, e_K, N)
    Lam2 = pow(node.st.Lambda_I, e_K, N)
    e_I = e_of(primegen, node.I)
    for j, v in zip(K, F_new):
        if not v:
            continue
        t = shamir_trick(S2, S_j[j], e_I, primegen.get(j), N)
        if t is None:
            raise ValueError(f"无法为新增位置 {j} 求更新密钥：ShamirTrick 同源自检失败")
        Lam2 = Lam2 * pow(t, v, N) % N

    home = [j for j in K if j in set(node.I)]
    if home:
        FI_new = tuple(node.FI) + tuple(F_new[K.index(j)] for j in home)
        return Opening(S2, Lam2, node.I + tuple(home)), node.I + tuple(home), FI_new
    return Opening(S2, Lam2, node.I), node.I, node.FI


def _push_del(session, delta, node, op_delta: UpdateDelta, old_values) -> PushedUpdate:
    K = op_delta.K
    if not K:
        raise ValueError("K 不能为空")
    n, k = delta.n, len(K)
    if tuple(K) != tuple(range(n - k, n)):
        raise ValueError(
            f"del 只能删末尾连续的下标；期望 {tuple(range(n - k, n))}，收到 {K}"
        )
    if not set(K) <= set(node.I):
        raise ValueError(f"发起删除的节点必须持有 {list(K)}")

    crs_n = session.crs_n_for(delta)
    pi_K = disagg(crs_n, list(node.I), list(node.FI), node.st, K)
    new_delta = Digest(U=pi_K.S_I, C=pi_K.Lambda_I, n=n - k)

    old = dict(old_values) if old_values is not None else {
        i: node.view.value_of(i) for i in K
    }
    witness = UpdateWitness(
        op="del", K=K, S_K=pi_K.S_I, F_K=tuple(old[i] for i in K), pi_K=pi_K
    )
    return PushedUpdate(new_delta, node, witness)


# ---------------------------------------------------------------------------
# ApplyUpdate —— 验证方
# ---------------------------------------------------------------------------

def apply_update(
    session,
    delta: Digest,
    node: StorageNode,
    op_delta: UpdateDelta,
    witness: UpdateWitness,
) -> AppliedUpdate:
    """``StrgNode.ApplyUpdate(δ, n, st, I, FI, op, ∆, Υ∆) → (b, δ′, n′, st′, J, F′_J)``。

    **第一步就是校验 :math:`\\Upsilon_\\Delta`**，没过就原样返回 ``ok=False``，
    ``delta`` / ``node`` 保持 ``None``。

    本函数**不读改动后的内容**：``mod`` 的旧值来自 :math:`\\Upsilon_\\Delta`，
    ``add`` 的新位置见证由公开的 :math:`U` 推出，``del`` 的新摘要就是
    :math:`\\Upsilon_\\Delta` 里的 ``π_K``。
    """
    if op_delta.op != witness.op:
        return AppliedUpdate(False, f"∆ 与 Υ∆ 的 op 不一致（{op_delta.op} vs {witness.op}）")
    if tuple(op_delta.K) != tuple(witness.K):
        return AppliedUpdate(False, f"∆ 与 Υ∆ 的 K 不一致（{list(op_delta.K)} vs {list(witness.K)}）")

    ok, why = witness.verify(session.crs.primegen, session.crs.N, delta.U)
    if not ok:
        return AppliedUpdate(False, why)

    try:
        if op_delta.op == "mod":
            new_delta, st_new, I_new, FI_new = _apply_mod(session, delta, node, op_delta, witness)
        elif op_delta.op == "add":
            new_delta, st_new, I_new, FI_new = _apply_add(session, delta, node, op_delta, witness)
        elif op_delta.op == "del":
            new_delta, st_new, I_new, FI_new = _apply_del(session, delta, node, op_delta, witness)
        else:
            return AppliedUpdate(False, f"未知的 op {op_delta.op!r}")
    except ValueError as exc:
        return AppliedUpdate(False, f"{exc}")

    new_node = _rebuild(session, new_delta, node, st_new, I_new, FI_new)

    # 除了 Υ∆ 自身要过校验，**更新后的本地视图也必须合法**。
    #
    # 这一步不能省：``mod`` 不改变 U，所以一份旧版本的 Υ∆ 仍能满足
    # S_K^{e_K} = U —— 单看那一条，重放攻击是过得去的。
    # 但重放会把 Δ 按旧值重算一遍，得到的 C′ 与节点实际存着的数据对不上，
    # check_local_view 立刻就能看出来。
    # 论文把 ApplyUpdate 的返回记为 b（只指 Υ∆ 校验），这里把
    # 「b = 1 且视图合法」一起作为接受条件 —— 这才是正确的定义里
    # 「更新后仍是合法本地视图」那一条。
    if new_node.I and not new_node.check_local_view():
        return AppliedUpdate(
            False,
            "更新后的本地视图不合法：Υ∆ 与本地数据对不上。"
            "最常见的原因是这份 Υ∆ 已经被应用过（重放），"
            "或者 Υ∆ 里声称的旧值与实际不符",
        )

    return AppliedUpdate(True, "", new_delta, new_node)


def _apply_mod(session, delta, node, op_delta, witness):
    K, F_new = op_delta.K, op_delta.F_new
    primegen, N = session.crs.primegen, session.crs.N

    if len(witness.F_K) != len(K):
        raise ValueError("Υ∆ 里的旧值个数与 K 不一致")
    deltas = {i: F_new[j] - witness.F_K[j] for j, i in enumerate(K)}

    S_i = _membership_witnesses(witness.S_K, K, primegen, N)
    C2 = delta.C
    for i in K:
        if deltas[i]:
            C2 = C2 * pow(S_i[i], deltas[i], N) % N
    new_delta = Digest(U=delta.U, C=C2, n=delta.n)

    st_new, I_new, FI_new = _mod_node_state(node, K, F_new, deltas, S_i, primegen, N)
    return new_delta, st_new, I_new, FI_new


def _apply_add(session, delta, node, op_delta, witness):
    F_new = op_delta.F_new
    primegen, N = session.crs.primegen, session.crs.N
    n = delta.n
    if len(F_new) != len(witness.K):
        raise ValueError("∆ 里的新值个数与 K 不一致")

    K = witness.K
    e_K = e_of(primegen, K)
    S_cur, Lam_cur = delta.U, delta.C
    for j, v in zip(K, F_new):
        S_cur, Lam_cur = add_back(S_cur, Lam_cur, primegen.get(j), v, N)
    new_delta = Digest(U=S_cur, C=Lam_cur, n=n + len(K))

    S_j = {j: pow(delta.U, e_K // primegen.get(j), N) for j in K}
    st_new, I_new, FI_new = _add_node_state(node, K, F_new, e_K, S_j, primegen, N)
    return new_delta, st_new, I_new, FI_new


def _apply_del(session, delta, node, op_delta, witness):
    K = witness.K
    pi_K = witness.pi_K
    if pi_K is None:
        raise ValueError("del 的 Υ∆ 里必须带 π_K（它就是新摘要）")

    n_new = delta.n - len(K)
    if len(witness.F_K) != len(K):
        raise ValueError("Υ∆ 里的旧值个数与 K 不一致")
    if node.st.S_I is None:
        raise ValueError("节点状态不完整")

    # 新摘要就是 π_K（与论文 δ' ← ((Γ_K, ∆_K), n') 一致），先算好
    new_delta = Digest(U=pi_K.S_I, C=pi_K.Lambda_I, n=n_new)

    I_set = set(node.I)
    if set(K) <= I_set:
        # 删掉的全在手里：J = I\K，而 (S_I, Λ_I) 一个字都不用改。
        #
        # S'_J = g^{e_[n']/e_J} = g^{e_[n]/(e_K·e_I/e_K)} = S_I，
        # Λ'_J 的连乘范围 [n']\J 与 [n]\I 是同一个集合、指数也相同。
        J = tuple(i for i in node.I if i not in set(K))
        if not J:
            # 数据被删光，节点下线。这里返回一个空视图，
            # 由调用方（_run_update）负责把它从节点列表里剔除。
            return new_delta, Opening(node.st.S_I, node.st.Lambda_I, ()), (), ()
        st_new = Opening(node.st.S_I, node.st.Lambda_I, J)
        FI_new = tuple(node.view.value_of(i) for i in J)
    elif not (set(K) & I_set):
        # 与删除区间不相交：新状态 = agg(π_I, π_K)
        merged = agg(
            session.crs_n_for(delta),
            list(node.I), list(node.FI), node.st,
            list(K), list(witness.F_K), pi_K,
        )
        # agg 返回的 .I 是并集，而 K 已经被删，要改回节点真正持有的部分
        J = node.I
        st_new = Opening(merged.S_I, merged.Lambda_I, J)
        FI_new = node.FI
    else:
        raise ValueError(
            f"{node.node_id} 的持有集合与 K 部分相交，本实现不支持这种情形；"
            f"请先把该节点的 K 部分 rmv_storage 掉再删除"
        )

    return new_delta, st_new, J, FI_new


# ---------------------------------------------------------------------------
# 系统级封装：把两段式串成「一次更新整个网络」
# ---------------------------------------------------------------------------

def _run_update(session, delta, nodes, op_delta, pusher, old_values) -> UpdateRecord:
    """对全部节点跑一遍 Push（在 pusher 上）+ Apply（在**每一个**节点上）。

    统一让所有节点都走 ``ApplyUpdate``（包括发起方），这样 Push 与 Apply
    两条路径必须给出同一个新状态 —— 每次更新顺带自检一次。
    任何一个节点的 :math:`\\Upsilon_\\Delta` 校验没过就整次失败。
    """
    pushed = push_update(session, delta, pusher, op_delta, old_values)

    new_nodes: list[StorageNode] = []
    changes: list[str] = []
    new_delta = pushed.delta

    for nd in nodes:
        out = apply_update(session, delta, nd, op_delta, pushed.witness)
        if not out.ok:
            raise ValueError(f"ApplyUpdate 在 {nd.node_id} 上失败：{out.message}")
        if out.node is None or not out.node.I:
            changes.append(f"{nd.node_id}: 数据已删光，下线")
            continue
        new_nodes.append(out.node)
        changes.append(
            f"{nd.node_id}: {'合法' if out.node.check_local_view() else '不合法'}"
        )

    rec = UpdateRecord(
        op=op_delta.op,
        K=op_delta.K,
        F_new=op_delta.F_new,
        new_delta=new_delta,
        witness=pushed.witness,
        notes=_notes_for(op_delta, delta, new_delta, pushed.witness),
        node_changes=changes,
        witness_ok=True,
    )
    rec.new_nodes = new_nodes
    return rec


def _notes_for(op_delta, old: Digest, new: Digest, witness: UpdateWitness) -> list[str]:
    base = [
        f"n: {old.n} → {new.n}",
        f"Υ∆ 校验：S_K^(e_K) = {'U′' if op_delta.op == 'add' else 'U'} 通过"
        f"（S_K 指纹 {fingerprint(witness.S_K)}）",
    ]
    if op_delta.op == "mod":
        base.append("U 不变；C 变了（值改了，承诺必然变）")
    elif op_delta.op == "add":
        base.append("U 与 C 都要变：对新位置依次 add_back")
    else:
        base.append("新摘要 δ' 直接就是 π_K = d(v \\ K)")
    return base


def update_modify(
    session,
    delta: Digest,
    nodes: Sequence[StorageNode],
    K: Sequence[int],
    F_new: Sequence[int],
) -> UpdateRecord:
    """``op = mod`` —— 改若干位置的值，文件长度不变。"""
    K_set = as_index_set(K)
    F_new = tuple(int(v) for v in F_new)
    if not K_set:
        raise ValueError("K 不能为空")
    if len(K_set) != len(F_new):
        raise ValueError("K 与 F_new 长度必须一致")
    if K_set[-1] >= delta.n:
        raise ValueError(f"下标 {K_set[-1]} 越界（当前 n = {delta.n}）")

    op_delta = UpdateDelta("mod", K_set, F_new)
    return _run_update(
        session, delta, nodes, op_delta, nodes[0], _old_values(nodes, K_set)
    )


def update_append(
    session,
    delta: Digest,
    nodes: Sequence[StorageNode],
    F_new: Sequence[int],
) -> UpdateRecord:
    """``op = add`` —— 在末尾追加若干位置，并指派一个新节点持有它们。"""
    F_new = tuple(int(v) for v in F_new)
    if not F_new:
        raise ValueError("至少要追加一个位置")

    n, k = delta.n, len(F_new)
    if n + k > session.n_max:
        raise ValueError(
            f"追加后长度 {n + k} 超过会话上限 n_max = {session.n_max}；"
            f"隐藏阶群的可用位置在 Bootstrap 阶段就定死了"
        )

    K = tuple(range(n, n + k))
    op_delta = UpdateDelta("add", K, F_new)
    rec = _run_update(session, delta, nodes, op_delta, nodes[0], None)

    # 新位置得有人存。它的证明就是**旧摘要本身**：
    #     π_K^new = d_new(v' \ K) = d_new(旧文件) = (U, C)
    # 因为「除 K 之外的其余部分」正是旧文件，所以不用算任何东西。
    rec.new_nodes.append(
        StorageNode(
            f"node-{len(nodes)}",
            session,
            LocalView(
                delta=rec.new_delta,
                st=Opening(delta.U, delta.C, K),
                I=K,
                FI=F_new,
            ),
        )
    )
    rec.notes.append(
        f"新增 {k} 个位置，指派 node-{len(nodes)} 持有（其证明即旧摘要）"
    )
    rec.node_changes.append(
        f"node-{len(nodes)}: "
        f"{'合法' if rec.new_nodes[-1].check_local_view() else '不合法'}"
    )
    return rec


def update_truncate(
    session,
    delta: Digest,
    nodes: Sequence[StorageNode],
    K: Sequence[int],
) -> UpdateRecord:
    """``op = del`` —— 删掉末尾的若干个位置。"""
    K_set = as_index_set(K)
    if not K_set:
        raise ValueError("K 不能为空")
    if tuple(K_set) != tuple(range(delta.n - len(K_set), delta.n)):
        raise ValueError(
            f"del 只能删末尾连续的下标；"
            f"期望 {tuple(range(delta.n - len(K_set), delta.n))}，收到 {K_set}"
        )

    holder = _holder_of(nodes, K_set)
    op_delta = UpdateDelta("del", K_set, ())
    rec = _run_update(
        session, delta, nodes, op_delta, holder, _old_values(nodes, K_set)
    )

    # K ⊆ I 且 I\K 为空的节点直接下线
    rec.new_nodes = [nd for nd in rec.new_nodes if nd.I]
    rec.node_changes = [
        f"{nd.node_id}: {'合法' if nd.check_local_view() else '不合法'}"
        for nd in rec.new_nodes
    ]
    rec.notes.append(
        "持有 K 的节点删掉即可（状态不用改）；与 K 不相交的节点做一次 agg"
    )
    return rec
