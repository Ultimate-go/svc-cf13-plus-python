"""端到端演示：论文 §8.1 的 ``VDS1``。

跟 ``demo/end_to_end.py``（§8.2 的 ``VDS2``）演示同一套流程，
但重点在 ``VDS1`` 独有的那两件事：

* **``CreateFrom`` / ``GetCreate``** —— 一个只存了文件一部分的节点，
  能从中派生出一个**新文件**并提供常数大小的 ``PoKSubV'`` 证明；
  客户端不用拿到内容就能确认新摘要确实是原文件那一段。
* **三种更新的本地状态维护** —— ``mod`` / ``del`` 要按
  :math:`I \\cap K` 的三种情形分别处理，演示里三种都跑一遍。

运行::

    python demo/vds1_create_from.py
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from svc import DeterministicRNG  # noqa: E402
from svc.types import fingerprint  # noqa: E402
from svc.yinyan import Opening1  # noqa: E402
from vds import (  # noqa: E402
    ClientNode1,
    CreateWitness,
    LocalView1,
    PushedUpdate1,
    StorageNode1,
    UpdateOp1,
    VDS1Session,
    com_prime,
)

N_MAX = 24
N = 12
LAMBDA = 32
MODULUS_BITS = 512


def rule(title: str) -> None:
    print("\n" + "=" * 72)
    print(title)
    print("=" * 72)


def _short(I) -> str:
    if not I:
        return ""
    if len(I) <= 6:
        return ",".join(str(i) for i in I)
    return f"{I[0]},…,{I[-1]}"


def show(node: StorageNode1) -> str:
    d = node.delta
    return (
        f"|I|={len(node.I):2d}  I=[{_short(node.I)}]  "
        f"δ=({fingerprint(d.A)}, {fingerprint(d.B)}, n={d.n})  "
        f"视图有效={node.check_local_view()}"
    )


def as_node(node_id: str, session: VDS1Session, res) -> StorageNode1:
    """把 ``AppliedUpdate1`` / ``PushedUpdate1`` 的结果包成新节点。"""
    return StorageNode1(node_id, session,
                        LocalView1(res.delta, res.st, res.J, res.F_J))


def make_root(session: VDS1Session, vals) -> tuple:
    delta, st = session.commit(vals)
    return delta, StorageNode1(
        "root", session,
        LocalView1(delta, st, list(range(len(vals))), list(vals)),
    )


def sub_of(session: VDS1Session, base: StorageNode1, I, node_id="part"):
    keep = list(I)
    drop = [i for i in base.I if i not in set(keep)]
    node = base.rmv_storage(drop) if drop else base
    return StorageNode1(node_id, session, node.view)


def main() -> None:  # noqa: C901 - 演示脚本，线性流程更好读
    t_all = time.time()

    # ------------------------------------------------------------------
    rule("0. Bootstrap —— 生成公开参数 pp 与空文件的 (δ₀, st₀)")
    # ------------------------------------------------------------------
    t0 = time.time()
    session = VDS1Session(
        n_max=N_MAX, k=1, lambda_bits=LAMBDA, modulus_bits=MODULUS_BITS,
        seed=b"vds1-demo",
    )
    delta0, st0 = session.bootstrap()
    print(f"pp        : {session}")
    print(f"隐藏阶群  : |N| = {session.crs.N.bit_length()} 位，g = {session.crs.g}")
    print(f"δ₀        : ((g₀, g₁), 0) = "
          f"({fingerprint(delta0.A)}, {fingerprint(delta0.B)}, 0)")
    print("st₀        : (g₀, g₁) —— 空文件的那份根打开")
    print(f"与 VC.Com'([]) 一致 : {com_prime(session.crs, []) == delta0}")
    print(f"[{time.time() - t0:.2f}s]")

    # ------------------------------------------------------------------
    rule(f"1. 提交一个 {N} 块的文件")
    # ------------------------------------------------------------------
    rng = DeterministicRNG(b"vds1-demo-file")
    vals = [rng.randbelow(2) for _ in range(N)]
    delta, root = make_root(session, vals)
    print(f"文件       : {''.join(str(v) for v in vals)}")
    print(f"δ          : ({fingerprint(delta.A)}, {fingerprint(delta.B)}, n={N})")
    print(f"root       : {show(root)}")

    # ------------------------------------------------------------------
    rule("2. 分发 —— 根节点把不同片段拆给三个存储节点")
    # ------------------------------------------------------------------
    nodes = {
        "A": sub_of(session, root, range(0, 6), "A"),
        "B": sub_of(session, root, range(6, 12), "B"),
        "C": sub_of(session, root, [9, 10], "C"),
    }
    for name, node in nodes.items():
        print(f"节点 {name}      : {show(node)}")
    print("注意：每个节点只存了自己那段 + 两个群元素的证据，没存整个文件。")

    # ------------------------------------------------------------------
    rule("3. 检索 + 独立验证（客户端只拿一个 δ）")
    # ------------------------------------------------------------------
    client = ClientNode1("client", session, delta)
    certs = []
    for name, Q in (("A", [0, 1, 2]), ("B", [7, 8]), ("C", [9, 10])):
        F_Q, pi_Q = nodes[name].retrieve(Q)
        print(f"节点 {name} 返回 Q={Q} F_Q={list(F_Q)} → 验证 "
              f"{client.ver_retrieve(Q, F_Q, pi_Q)}")
        certs.append((Q, F_Q, pi_Q))

    merged = client.aggregate_certificates(certs)
    allQ = [0, 1, 2, 7, 8, 9, 10]
    values_at = [vals[i] for i in allQ]
    print(f"\n三份证据聚合成一个（{len(merged.Gamma)} 个群元素）→ 整体验证 "
          f"{client.ver_retrieve(allQ, values_at, merged)}")

    tampered = Opening1(
        (merged.Gamma[0] * 3 % session.crs.N,), merged.Delta, merged.I
    )
    print(f"把聚合证据改一下再验 → "
          f"{client.ver_retrieve(allQ, values_at, tampered)}")

    # ------------------------------------------------------------------
    rule("4. CreateFrom / GetCreate —— 从已存文件派生新文件")
    # ------------------------------------------------------------------
    M = 5
    J = list(range(M))
    t0 = time.time()
    derived, upsilon = nodes["A"].create_from(J)
    print(f"节点 A（只存了 [0..5]）派生出前 {M} 块构成的新文件 F_J")
    print(f"新摘要 δ'  : ({fingerprint(upsilon.delta.A)}, "
          f"{fingerprint(upsilon.delta.B)}, n={upsilon.delta.n})")
    print(f"δ' == Com'(F_J) : {upsilon.delta == com_prime(session.crs, vals[:M])}")
    print(f"派生节点   : {show(derived)}")
    print("Υ_J 大小   : 9 个群元素 + 2 个标量，与 |J| 无关")
    print(f"[{time.time() - t0:.2f}s]")

    ok, delta_p = client.get_create(J, upsilon)
    print(f"\n客户端跑 PoKSubV'.V → {ok}")
    print(f"客户端接受的新摘要 δ' == 发布方的 : {delta_p == upsilon.delta}")

    sub_client = ClientNode1("sub", session, delta_p)
    F_Q, pi_Q = derived.retrieve([0, 3, 4])
    print(f"子文件检索 Q=[0,3,4] → 验证 "
          f"{sub_client.ver_retrieve([0, 3, 4], F_Q, pi_Q)}")

    forged = CreateWitness(
        delta=com_prime(session.crs, vals[1:M + 1]), proof=upsilon.proof
    )
    print(f"把 δ' 换成另一段子向量的承诺 → {client.get_create(J, forged)[0]}")
    print(f"J 改成非前缀 [1,2,3] → {client.get_create([1, 2, 3], upsilon)[0]}")

    # ------------------------------------------------------------------
    rule("5. 更新 —— mod，三种 I ∩ K 情形")
    # ------------------------------------------------------------------
    K = [3, 4]
    F_new = [vals[i] ^ 1 for i in K]
    op_mod = UpdateOp1("mod", K, F_new)
    pushed = root.push_update(op_mod)
    vals_mod = list(vals)
    for pos, i in enumerate(K):
        vals_mod[i] = F_new[pos]

    print(f"把位置 {K} 改成 {F_new}（其余不动）")
    print(f"新摘要     : ({fingerprint(pushed.delta.A)}, "
          f"{fingerprint(pushed.delta.B)}, n={pushed.delta.n})")
    print(f"δ' == 重新提交整个文件 : "
          f"{pushed.delta == com_prime(session.crs, vals_mod)}")
    print(f"Υ_∆ 里的旧值 F_K = {list(pushed.F_K)}，它对 δ 仍然有效 : "
          f"{client.ver_retrieve(K, list(pushed.F_K), pushed.pi_K)}")
    print(f"客户端 ApplyUpdate → {client.apply_update(op_mod, pushed)[0]}")
    print("注意：摘要变了，但发布者自己的本地状态一个字都不用改 ——")
    print("      因为 K ⊆ I 时新值带来的指数因子在 Γ_I 里正好约掉。")

    updated = {}
    for name in ("A", "B", "C"):
        node = nodes[name]
        res = node.apply_update(op_mod, pushed)
        if set(K) <= set(node.I):
            kind = "I∩K=K"
        elif not (set(K) & set(node.I)):
            kind = "I∩K=∅"
        else:
            kind = "I∩K=L"
        if not res.ok:
            print(f"节点 {name}（{kind}）→ 被拒！")
            continue
        new = as_node(name, session, res)
        print(f"节点 {name}（{kind:<6}）→ 新 I={_short(new.I):<12} "
              f"视图有效={new.check_local_view()}")
        updated[name] = new
    nodes = updated
    root = as_node("root", session, pushed)

    # ------------------------------------------------------------------
    rule("6. 更新 —— add / del")
    # ------------------------------------------------------------------
    op_add = UpdateOp1("add", [N, N + 1], [1, 0])
    pushed_add = root.push_update(op_add)
    vals_add = vals_mod + [1, 0]
    print(f"add 追加 [N, N+1]：δ' == 重新提交 ? "
          f"{pushed_add.delta == com_prime(session.crs, vals_add)}，"
          f"n = {pushed_add.delta.n}")
    root = as_node("root", session, pushed_add)

    op_del = UpdateOp1("del", [N, N + 1])
    pushed_del = root.push_update(op_del)
    print(f"del 删掉末尾 [N, N+1]：δ' == 重新提交 ? "
          f"{pushed_del.delta == com_prime(session.crs, vals_mod)}，"
          f"n = {pushed_del.delta.n}")
    print(f"add 再 del 回来，摘要与 mod 之后完全相同 : "
          f"{pushed_del.delta == pushed.delta}")

    tail = sub_of(session, root, [10, 11, 12, 13], "tail")
    res = tail.apply_update(op_del, pushed_del)
    tail_new = as_node("tail", session, res)
    print(f"\n节点 tail（I=[10,11,12,13]，I∩K=K）接受 del → {res.ok}，"
          f"新 I={list(res.J)}，视图有效={tail_new.check_local_view()}")

    # ------------------------------------------------------------------
    rule("7. 攻击面")
    # ------------------------------------------------------------------
    # 把旧值里的一位翻过来 —— 零集合变了，旧证据就对不上了。
    # （注意不能拿 F_new 冒充旧值：若它恰好给出同一个零集合，就不是伪造）
    forged_push = PushedUpdate1(
        delta=pushed.delta, st=pushed.st, J=pushed.J, F_J=pushed.F_J,
        F_K=(pushed.F_K[0] ^ 1, pushed.F_K[1]), pi_K=pushed.pi_K,
    )
    print(f"Υ_∆ 里的旧值被翻转一位 → 节点 C 接受 ? "
          f"{nodes['C'].apply_update(op_mod, forged_push).ok}")

    replay_client = ClientNode1("replay", session, pushed.delta)
    print(f"把同一份 Υ_∆ 重放到新摘要上 → "
          f"{replay_client.apply_update(op_mod, pushed)[0]}")

    stale_client = ClientNode1("stale", session, delta)
    print(f"用 n={delta.n} 的陈旧摘要做 del [N,N+1] → "
          f"{stale_client.apply_update(op_del, pushed_del)[0]}")
    print(f"用 n={pushed_del.delta.n} 的摘要重复做一次 del → "
          f"{ClientNode1('x', session, pushed_del.delta).apply_update(op_del, pushed_del)[0]}")

    rule(f"总耗时 {time.time() - t_all:.2f}s")


if __name__ == "__main__":
    main()
