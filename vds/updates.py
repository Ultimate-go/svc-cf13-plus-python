"""文件更新操作 —— 论文 §8.2 的 ``StrgNode.PushUpdate`` / ``ApplyUpdate``。

三种操作
--------
========  =========================================================
``op``     语义
========  =========================================================
``mod``    改若干位置的值，文件长度不变
``add``    在末尾追加若干个位置
``del``    删掉末尾的若干个位置
========  =========================================================

.. warning::

   **与论文 §8.2 的一处重要出入（如实说明）**

   论文 §8.2 的 ``PushUpdate``/``ApplyUpdate`` 正文里用的是 **§5.1 阴阳方案**的原语：

   .. code-block:: text

      执行 πK ← VC.Disagg′(pp, I, FI, πI, K) 并解析 πK := (ΓK, ∆K)
      然后计算 (a′K, b′K) ← PartndPrimeProd(K, F′K)
      并令 δ′ ← ((Γ^{a′K}_K, ∆^{b′K}_K), n′)

   ``Γ/∆`` 是 §5.1 的阴阳累加器对，``PartndPrimeProd`` 是 §5.1 的二元划分，
   而 §8.2 的摘要却是 :math:`\\delta = ((U, C), n)` 这个 §5.2 的形式。
   也就是说：**§8.2 的更新算法正文是从 §8.1 抄过来的，没有真正改成 §5.2 的记号**，
   逐字转写是做不到的。

   本模块因此**从摘要代数独立推导**三个更新公式，并用 :func:`svc.verify` 独立验证
   每一步的结果 —— 只要更新后所有节点的本地视图仍然合法、检索仍然能通过验证，
   公式就是对的（这一点由 ``tests/test_updates.py`` 逐条钉死）。

三个公式的推导
--------------
记号：节点持有 :math:`\\pi_I = d(\\mathbf{v} \\setminus I) = (S_I, \\Lambda_I)`。

**``mod``**（:math:`n` 不变，故 :math:`U` 与 :math:`S_I` 都不变）::

    C'        = C · ∏_{i∈K} S_i^{Δ_i},   Δ_i = v'_i − v_i
    Λ'_I      = Λ_I · ∏_{i∈K\\I} (S_I^{1/e_i})^{Δ_i}

:math:`\\Lambda_I` 只含 :math:`j \\notin I` 的值，所以**被改的位置若在 ``I`` 里则完全不影响 ``Λ_I``**。
剩下的修正项里 :math:`S_I^{1/e_i}` 就是 :math:`\\text{ShamirTrick}(S_I, S_i, e_I, e_i)`
（两个根都来自同一个 :math:`U`，且 :math:`\\gcd(e_I,e_i)=1`，因为 :math:`i \\notin I`）。

**``add``**（:math:`n' = n+k`，:math:`e_{[n']} = e_{[n]}\\cdot e_K`）::

    S'_I      = S_I^{e_K}
    Λ'_I      = Λ_I^{e_K} · ∏_{j∈K} (S'_I^{1/e_j})^{v_j}

其中 :math:`S'_I^{1/e_j} = \\text{ShamirTrick}(S'_I, S'_j, e_I, e_j)`，
而新位置的成员见证 :math:`S'_j = U^{e_K/e_j}`。

摘要这一侧更干净：**就是对新位置顺序做一次 ``add_back``** ——
对单个新位置恰好是资料里那条 :math:`S'=S^{e_{n+1}},\\ \\Lambda'=\\Lambda^{e_{n+1}}S^{v_{n+1}}`。

**``del``**（删掉末尾的 :math:`K`，:math:`n' = n-|K|`）::

    新摘要 δ' = π_K = d(v \\ K)          ← 就是 K 上的拆分证明，与论文一致

* 若 :math:`K \\subseteq I`：节点变成 :math:`J = I \\setminus K`，而
  :math:`(S_J, \\Lambda_J)` **一个字节都不用改** ——
  因为 :math:`S'_J = g^{e_{[n']}/e_J} = g^{e_{[n]}/(e_K\\cdot e_I/e_K)} = S_I`。
* 若 :math:`I \\cap K = \\varnothing`：节点的新状态就是 :math:`\\text{agg}(\\pi_I, \\pi_K)`
  （两者不相交，正好用得上聚合）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from svc import (
    CRSn,
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
from .storage_node import StorageNode

__all__ = [
    "UpdateRecord",
    "update_modify",
    "update_append",
    "update_truncate",
]


@dataclass
class UpdateRecord:
    """一次更新的结果，供演示与审计使用。"""

    op: str
    K: tuple[int, ...]
    F_new: tuple[int, ...]
    new_delta: Digest
    new_nodes: list = field(default_factory=list)
    witness: dict = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)
    node_changes: list[str] = field(default_factory=list)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"UpdateRecord(op={self.op!r}, K={list(self.K)}, "
            f"→ {self.new_delta!r})"
        )


# ---------------------------------------------------------------------------
# 公共小工具
# ---------------------------------------------------------------------------

def _membership_witnesses(
    session, S_K: int, K: Sequence[int]
) -> dict[int, int]:
    """由聚合成一体的 :math:`S_K` 反推出 :math:`K` 里每个位置的成员见证 :math:`S_i`。

    .. math::
        S_K^{\\,e_K/e_i} = \\left(g^{e_{[n]}/e_K}\\right)^{e_K/e_i}
                        = g^{e_{[n]}/e_i} = S_i

    这正是论文让存储节点把 :math:`S_K` 交给客户端当「更新密钥」的原因：
    一个群元素就够客户端推出整批 :math:`S_i`，不用逐个索取。
    """
    pg, N = session.crs.primegen, session.crs.N
    es = [pg.get(i) for i in K]
    return dict(zip(K, batch_root_factor_any(S_K, es, N)))


def _holder_of(nodes: Sequence[StorageNode], K: Sequence[int]) -> StorageNode:
    need = set(K)
    for nd in nodes:
        if need <= set(nd.I):
            return nd
    raise ValueError(
        f"没有任何节点完整持有下标 {sorted(need)}；"
        f"请先让节点用 add_storage 合并出所需区间"
    )


def _subset_S(session, delta: Digest, nodes: Sequence[StorageNode], K) -> int:
    """求 :math:`S_K = g^{e_{[n]}/e_K}`。

    优先从一个完整持有 ``K`` 的节点那里**拆**出来（:math:`O(\\ell|I\\setminus K|)`）——
    这是 VDS 里该走的路。若 ``K`` 横跨多个节点（没有单个节点持有全部），
    则退回直接计算一次模幂。
    """
    K_set = set(K)
    for nd in nodes:
        if K_set <= set(nd.I):
            return disagg(
                session.crs_n_for(delta),
                list(nd.I),
                list(nd.FI),
                nd.st,
                K,
            ).S_I
    # 退化路径：一次指数约 n(ℓ+1) 位的模幂
    crs_n = session.crs_n_for(delta)
    return pow(
        session.crs.g,
        crs_n.e_all // e_of(session.crs.primegen, K),
        session.crs.N,
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
    new_values: dict[int, int] | None = None,
) -> StorageNode:
    """用新的 ``st``（以及可选的新值）重建一个节点。

    :param new_values: ``{下标: 新值}``。**改值时必须传** ——
                       否则节点会拿着旧值去验证新证据，本地视图必然不过。
    """
    FI = list(nd.FI)
    if new_values:
        for pos, i in enumerate(nd.I):
            if i in new_values:
                FI[pos] = int(new_values[i])
    return StorageNode(
        nd.node_id,
        session,
        LocalView(delta=delta, st=st, I=nd.I, FI=tuple(FI)),
    )


# ---------------------------------------------------------------------------
# op = mod
# ---------------------------------------------------------------------------

def update_modify(
    session,
    delta: Digest,
    nodes: Sequence[StorageNode],
    K: Sequence[int],
    F_new: Sequence[int],
) -> UpdateRecord:
    """``op = mod`` —— 改若干位置的值，文件长度不变。

    :param K: 被改的下标
    :param F_new: 与 ``K`` 一一对应的新值
    :returns: :class:`UpdateRecord`，其中 ``new_delta`` 是客户端的新摘要，
              ``nodes`` 由调用方从这里取（见 ``record.node_changes`` 的说明）

    .. note::

       本函数**不修改**传入的 ``nodes``，新的节点列表通过
       :attr:`UpdateRecord.notes` 之外的方式返回是不方便的，
       所以更推荐用 :func:`apply_modify` 这种「直接换掉列表」的封装。
       这里保留两个函数是为了和论文的
       ``PushUpdate``（节点产出）+ ``ApplyUpdate``（客户端确认）
       两段式结构对应。
    """
    K = as_index_set(K)
    F_new = tuple(int(v) for v in F_new)
    if not K:
        raise ValueError("K 不能为空")
    if len(K) != len(F_new):
        raise ValueError("K 与 F_new 长度必须一致")
    n = delta.n
    if K[-1] >= n:
        raise ValueError(f"下标 {K[-1]} 越界（当前 n = {n}）")

    pg, N = session.crs.primegen, session.crs.N

    # 旧值 → 差值（K 可以横跨多个节点，所以逐下标去查）
    old = _old_values(nodes, K)
    deltas = {i: (F_new[j] - old[i]) for j, i in enumerate(K)}

    # 更新密钥：S_K，再由它推出每个 S_i
    S_K = _subset_S(session, delta, nodes, K)
    S_i = _membership_witnesses(session, S_K, K)

    # ---- 新承诺 ----
    C2 = delta.C
    for i in K:
        if deltas[i]:
            C2 = C2 * pow(S_i[i], deltas[i], N) % N
    new_delta = Digest(U=delta.U, C=C2, n=n)

    # ---- 各节点的新状态 ----
    new_nodes: list[StorageNode] = []
    for nd in nodes:
        outside = [i for i in K if i not in set(nd.I)]
        inside = [i for i in K if i in set(nd.I)]
        if not outside:
            # 改动的位置全在 I 里 → Λ_I 不含这些值，完全不变
            st_new = nd.st
            note = f"{nd.node_id}: 改动位置都在 I 内，状态不变"
        else:
            e_I = e_of(pg, nd.I)
            Lam = nd.st.Lambda_I
            for i in outside:
                if not deltas[i]:
                    continue
                t = shamir_trick(nd.st.S_I, S_i[i], e_I, pg.get(i), N)
                if t is None:
                    raise ValueError(
                        f"{nd.node_id}: 无法为下标 {i} 求更新密钥 "
                        f"（ShamirTrick 失败，说明 i 落在了 I 里）"
                    )
                Lam = Lam * pow(t, deltas[i], N) % N
            st_new = Opening(nd.st.S_I, Lam, nd.I)
            note = (
                f"{nd.node_id}: 修正 {len(outside)} 个 I 外的位置"
                f"（{inside and f'{len(inside)} 个在 I 内无需修正' or ''}）"
            )
        new_nodes.append(
            _rebuild(
                session,
                new_delta,
                nd,
                st_new,
                new_values={i: F_new[j] for j, i in enumerate(K)},
            )
        )

    rec = UpdateRecord(
        op="mod",
        K=K,
        F_new=F_new,
        new_delta=new_delta,
        witness={
            "op": "mod",
            "K": list(K),
            "S_K": hex(S_K),
            "S_K_fp": fingerprint(S_K),
            "F_K_old": [old[i] for i in K],
            "F_K_new": list(F_new),
        },
        notes=[
            f"n 不变（{n}），U 不变",
            f"C 由 {fingerprint(delta.C)} 变为 {fingerprint(C2)}",
            "客户端只拿到一个 S_K，即可用 root_factor 推出全部 S_i",
        ],
        node_changes=[f"{nd.node_id}: {'合法' if nd.check_local_view() else '不合法'}"
                      for nd in new_nodes],
    )
    rec.new_nodes = new_nodes
    return rec


# ---------------------------------------------------------------------------
# op = add
# ---------------------------------------------------------------------------

def update_append(
    session,
    delta: Digest,
    nodes: Sequence[StorageNode],
    F_new: Sequence[int],
) -> UpdateRecord:
    """``op = add`` —— 在末尾追加若干个位置。"""
    F_new = tuple(int(v) for v in F_new)
    if not F_new:
        raise ValueError("至少要追加一个位置")
    n = delta.n
    k = len(F_new)
    if n + k > session.n_max:
        raise ValueError(
            f"追加后长度 {n + k} 超过会话上限 n_max = {session.n_max}；"
            f"隐藏阶群的可用位置在 Bootstrap 阶段就定死了"
        )

    pg, N = session.crs.primegen, session.crs.N
    K = tuple(range(n, n + k))
    e_K = e_of(pg, K)

    # ---- 新摘要：对 (U, C) 顺序 add_back ----
    S_cur, Lam_cur = delta.U, delta.C
    for j, v in zip(K, F_new):
        S_cur, Lam_cur = add_back(S_cur, Lam_cur, pg.get(j), v, N)
    new_delta = Digest(U=S_cur, C=Lam_cur, n=n + k)

    # ---- 新位置的成员见证：S'_j = U^{e_K/e_j}（当前 U，即旧累加器）----
    S_j = {j: pow(delta.U, e_K // pg.get(j), N) for j in K}

    # ---- 各节点的新状态 ----
    new_nodes: list[StorageNode] = []
    for nd in nodes:
        e_I = e_of(pg, nd.I)
        S2 = pow(nd.st.S_I, e_K, N)
        Lam2 = pow(nd.st.Lambda_I, e_K, N)
        for j, v in zip(K, F_new):
            if not v:
                continue
            t = shamir_trick(S2, S_j[j], e_I, pg.get(j), N)
            if t is None:
                raise ValueError(f"{nd.node_id}: 无法为新增位置 {j} 求更新密钥")
            Lam2 = Lam2 * pow(t, v, N) % N
        new_nodes.append(
            _rebuild(session, new_delta, nd, Opening(S2, Lam2, nd.I))
        )

    # ---- 新位置得有人存：指派一个新节点持有 K ----
    #
    # 它的证明恰好就是**旧摘要本身**，这一点值得记一笔：
    #     π_K^{new} = d_new(v' \ K) = d_new(旧文件) = (U, C)
    # 因为「除 K 之外的其余部分」就是旧文件。所以不用算任何东西。
    # 验证一下两个分量：
    #     S_K = g^{e_[n']/e_K} = g^{e_[n]} = U
    #     Λ_K = ∏_{j∉K}(g^{e_[n]/e_j})^{v_j} = C
    new_nodes.append(
        StorageNode(
            f"node-{len(nodes)}",
            session,
            LocalView(
                delta=new_delta,
                st=Opening(delta.U, delta.C, K),
                I=K,
                FI=tuple(F_new),
            ),
        )
    )

    rec = UpdateRecord(
        op="add",
        K=K,
        F_new=F_new,
        new_delta=new_delta,
        witness={
            "op": "add",
            "K": list(K),
            "e_K_bits": e_K.bit_length(),
            "U_new_fp": fingerprint(S_cur),
        },
        notes=[
            f"n: {n} → {n + k}",
            f"U' = U^{{e_K}}（e_K 有 {e_K.bit_length()} 位）",
            "摘要侧就是对每个新位置做一次 add_back",
        ],
        node_changes=[
            f"{nd.node_id}: {'合法' if nd.check_local_view() else '不合法'}"
            for nd in new_nodes
        ],
    )
    rec.new_nodes = new_nodes
    return rec


# ---------------------------------------------------------------------------
# op = del
# ---------------------------------------------------------------------------

def update_truncate(
    session,
    delta: Digest,
    nodes: Sequence[StorageNode],
    K: Sequence[int],
) -> UpdateRecord:
    """``op = del`` —— 删掉末尾的若干个位置。

    要求 ``K`` 恰好是**末尾连续**的 :math:`|K|` 个下标
    （论文的 ``del`` 也只允许删末尾：``Ki = {ni−1−|Ki|+1, …, ni−1}``）。
    """
    K = as_index_set(K)
    if not K:
        raise ValueError("K 不能为空")
    n = delta.n
    k = len(K)
    if tuple(K) != tuple(range(n - k, n)):
        raise ValueError(
            f"del 只能删末尾连续的下标；期望 {tuple(range(n - k, n))}，收到 {K}"
        )

    pg, N = session.crs.primegen, session.crs.N
    crs_n = session.crs_n_for(delta)
    holder = _holder_of(nodes, K)

    # ---- 新摘要就是 K 上的拆分证明（与论文 δ' ← ((Γ_K, ∆_K), n') 一致）----
    pi_K = disagg(crs_n, list(holder.I), list(holder.FI), holder.st, K)
    new_delta = Digest(U=pi_K.S_I, C=pi_K.Lambda_I, n=n - k)

    # ---- 各节点的新状态 ----
    new_nodes: list[StorageNode] = []
    for nd in nodes:
        I_set = set(nd.I)
        if set(K) <= I_set:
            # 删掉的位置全在手里：剩下 J = I\K，而 (S_I, Λ_I) 一个字都不用改
            #
            # 代数依据：S'_J = g^{e_[n']/e_J} = g^{e_[n]/(e_K·e_I/e_K)} = S_I，
            #           Λ'_J 的连乘范围 [n']\J 与 [n]\I 是同一个集合、指数也相同，
            #           所以 Λ'_J = Λ_I。
            J = tuple(i for i in nd.I if i not in set(K))
            if not J:
                continue  # 这个节点的数据被删光了，直接下线
            # 注意要重新包一个 Opening：旧对象的 .I 还带着已删掉的下标，
            # 而 verify 的形状检查会拿它和视图里的 I 比对。
            st_new = Opening(nd.st.S_I, nd.st.Lambda_I, J)
            note = f"{nd.node_id}: J = I\\K，状态原封不动（S_I、Λ_I 都不变）"
        elif not (set(K) & I_set):
            # 与删除区间不相交：新状态 = agg(π_I, π_K)
            #
            # 注意 agg 返回的 Opening.I 是并集 I∪K，而 K 已经被删了，
            # 所以要把 I 改回本节点真正持有的那部分 —— 否则 verify
            # 的形状检查会因为「证明里的下标 ≠ 传入的下标」而直接拒绝。
            merged = agg(
                crs_n,
                list(nd.I), list(nd.FI), nd.st,
                list(K), list(holder.view.value_of(i) for i in K), pi_K,
            )
            st_new = Opening(merged.S_I, merged.Lambda_I, nd.I)
            J = nd.I
            note = f"{nd.node_id}: 与 K 不相交，状态 = agg(π_I, π_K)"
        else:
            raise ValueError(
                f"{nd.node_id} 的持有集合与 K 部分相交，本实现不支持这种情形；"
                f"请先把该节点的 K 部分 rmv_storage 掉再删除"
            )

        new_nodes.append(
            StorageNode(
                nd.node_id,
                session,
                LocalView(
                    delta=new_delta,
                    st=st_new,
                    I=J,
                    FI=tuple(_value_source(nd, holder, i) for i in J),
                ),
            )
        )

    rec = UpdateRecord(
        op="del",
        K=K,
        F_new=tuple(holder.view.value_of(i) for i in K),
        new_delta=new_delta,
        witness={
            "op": "del",
            "K": list(K),
            "S_K_fp": fingerprint(pi_K.S_I),
            "Lambda_K_fp": fingerprint(pi_K.Lambda_I),
        },
        notes=[
            f"n: {n} → {n - k}",
            f"新摘要 δ' 直接就是 π_K = d(v \\ K)，与论文一致",
            "持有 K 的节点删掉即可，状态不用改；其他节点做一次 agg",
        ],
        node_changes=[
            f"{nd.node_id}: {'合法' if nd.check_local_view() else '不合法'}"
            for nd in new_nodes
        ],
    )
    rec.new_nodes = new_nodes
    return rec


def _value_source(nd: StorageNode, holder: StorageNode, i: int) -> int:
    """取下标 ``i`` 的值：优先从本节点取，取不到就从持有者那里取。

    只用于 ``del`` 之后重建 :class:`LocalView` 的 ``FI`` ——
    删末尾时，所有剩余位置的值两个节点必有一个知道。
    """
    try:
        return nd.view.value_of(i)
    except KeyError:
        return holder.view.value_of(i)
