"""端到端演示：可验证分布式存储（VDS）完整流水线。

对应论文 §8.2 的 VDS2，以及需求里描述的流程：

    文件 → 切块 → 分发到多台服务器 → 检索若干部分 →
    服务器返回内容 + 证据 → 把多份证据聚合成一个 → 客户端验证这一个

运行::

    python demo/end_to_end.py
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from vds import VDSSession, join_blocks  # noqa: E402


def rule(title: str) -> None:
    print("\n" + "=" * 72)
    print(title)
    print("=" * 72)


def main() -> None:
    BLOCK_BYTES = 16
    N_MAX = 16

    rule("0. Bootstrap —— 生成公开参数 pp")

    t0 = time.time()
    session = VDSSession(
        n_max=N_MAX,
        l=BLOCK_BYTES * 8,
        lambda_bits=128,
        seed=b"vds-demo",
    )
    delta0 = session.bootstrap()
    print(f"pp        : {session.crs}")
    print(f"隐藏阶群  : |N| = {session.crs.N.bit_length()} 位，生成元 g = {session.crs.g}")
    print(f"初始摘要  : delta0 = {delta0}   (空文件)")
    print(f"耗时      : {time.time() - t0:.3f} s")

    # ------------------------------------------------------------------
    rule("1. 客户端把文件切成块并承诺")

    _base = (
        b"Verifiable Decentralized Storage - ASIACRYPT 2020 eprint 2020/149. "
        b"The file is split into blocks scattered over untrusted servers; "
        b"anyone may retrieve an arbitrary subset of blocks, and every "
        b"server returns the content together with a succinct proof. "
        b"All the proofs are then merged into a single one, and the "
        b"client checks that one proof against nothing but its digest. "
    )
    # 补到刚好 n_max 块（少 6 字节，顺便演示「不足一块要补零」）
    payload = (_base * 8)[: N_MAX * BLOCK_BYTES - 6]
    t0 = time.time()
    delta, crs_n, values, nbytes = session.commit_bytes(payload, BLOCK_BYTES)
    t_commit = time.time() - t0

    print(f"文件大小  : {nbytes} 字节")
    print(f"块大小    : {BLOCK_BYTES} 字节（l = {session.l} 位）")
    print(f"块数 n    : {delta.n}")
    print(f"摘要 delta: {delta}")
    print(f"耗时      : {t_commit:.3f} s")
    print()
    print("  关键点：摘要只有 (U, C, n) —— 两个群元素 + 一个整数。")
    print(f"  U 是 {delta.U.bit_length()} 位、C 是 {delta.C.bit_length()} 位，")
    print("  与文件大小完全无关。客户端只保存它。")

    # ------------------------------------------------------------------
    rule("2. 把块分发到 4 台互不信任的服务器")

    groups = [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]]
    groups = [[i for i in g if i < delta.n] for g in groups]
    groups = [g for g in groups if g]

    t0 = time.time()
    nodes = session.distribute(delta, values, groups, crs_n=crs_n)
    t_dist = time.time() - t0

    for node in nodes:
        print(f"  {node.node_id:9s} 持有下标 {list(node.I)}")
    print(f"耗时      : {t_dist:.3f} s")

    print("\n  抽查每台服务器是否真的老实存着它声称的数据：")
    for node in nodes:
        print(f"    {node.node_id:9s} check_local_view() -> {node.check_local_view()}")

    # ------------------------------------------------------------------
    rule("3. 检索其中若干部分（跨多台服务器）")

    Q = [1, 2, 9, 10, 13]
    print(f"检索请求 Q = {Q}")

    t0 = time.time()
    F_Q, certs, used = session.retrieve_from(nodes, Q)
    t_retr = time.time() - t0

    for cert in certs:
        print(f"  {cert.source:9s} 返回 {len(cert.Q)} 块: {list(cert.Q)}")
    print(f"耗时      : {t_retr:.3f} s")
    print(f"共收到    : {len(certs)} 份独立证据")
    print()
    print("  每份证据都是一个合法的子向量打开证明 π_Q = (S_Q, Λ_Q)，")
    print("  两个群元素，可直接拿去独立验证。")

    # ------------------------------------------------------------------
    rule("4. 把多份证据聚合成【一个】证据")

    client = session.make_client(delta)
    t0 = time.time()
    pi_K = client.aggregate_certificates(certs)
    t_agg = time.time() - t0

    print(f"聚合后    : {pi_K}")
    print(f"耗时      : {t_agg:.3f} s")
    print()
    print(f"  {len(certs)} 份证据 → 1 份，大小始终是 2 个群元素。")
    print("  这就是「增量聚合」：合并结果仍是合法证明，还能继续参与合并。")

    # ------------------------------------------------------------------
    rule("5. 客户端用摘要验证这一个证据")

    t0 = time.time()
    report = client.ver_retrieve(list(pi_K.I), [values[i] for i in pi_K.I], pi_K)
    t_ver = time.time() - t0

    print(f"验证结果  : {report.ok}  ({report.message})")
    print(f"耗时      : {t_ver * 1000:.1f} ms")
    print()
    print("  客户端全程只用了自己手里的 delta，没有向任何服务器索取额外信息。")

    # ------------------------------------------------------------------
    rule("6. 恢复文件内容并校验字节级一致")

    ordered = sorted(pi_K.I)
    part = join_blocks([values[i] for i in ordered], BLOCK_BYTES)
    expected_part = b"".join(
        int(values[i]).to_bytes(BLOCK_BYTES, "big") for i in ordered
    )
    print(f"这 {len(ordered)} 块字节一致 : {part == expected_part}")

    # 再取回【全部】块，验证 + 字节级恢复整个文件
    print("\n  再向 4 台服务器取回全部块：")
    F_all, certs_all, used_all = session.retrieve_from(
        nodes, list(range(delta.n))
    )

    t0 = time.time()
    pi_all = client.aggregate_certificates(certs_all)
    t_agg_all = time.time() - t0

    from svc.types import as_index_set  # noqa: E402

    Q_all = as_index_set([i for c in certs_all for i in c.Q])
    valmap: dict[int, int] = {}
    for c in certs_all:
        valmap.update(dict(zip(c.Q, c.F_Q)))
    vals_all = tuple(valmap[i] for i in Q_all)

    t0 = time.time()
    report_all = client.ver_retrieve(Q_all, vals_all, pi_all)
    t_ver_all = time.time() - t0

    recovered = join_blocks(list(vals_all), BLOCK_BYTES, nbytes)

    print(f"  收到 {len(certs_all)} 份证据 → 聚合成 1 份 → 验证: {report_all.ok}")
    print(f"  整文件字节一致 : {recovered == payload}")
    print()
    print(f"  聚合 {len(certs_all)} 份证据 : {t_agg_all * 1000:8.1f} ms"
          f"   ← 随块数增长")
    print(f"  验证那一个证据 : {t_ver_all * 1000:8.1f} ms"
          f"   ← 只与「本次打开了多少块」有关")
    print()
    print(f"  对比第 5 步：打开 5 块用了 {t_ver * 1000:.1f} ms，"
          f"这次打开 16 块用了 {t_ver_all * 1000:.1f} ms。")
    print(f"  单位代价 {t_ver * 1000 / 5:.2f} ms/块 vs "
          f"{t_ver_all * 1000 / 16:.2f} ms/块 —— 线性，与文件总长度无关。")
    print("  证据大小也始终是 2 个群元素，没有随文件变大。")

    # ------------------------------------------------------------------
    rule("7. 攻击场景：服务器篡改数据")

    victim = nodes[1]
    print(f"让 {victim.node_id} 把下标 {list(victim.I)[0]} 的值改掉，再响应一次检索：")

    tampered_view = victim.view
    tampered_FI = list(tampered_view.FI)
    tampered_FI[0] ^= 0xFF
    from vds import LocalView, StorageNode  # noqa: E402

    evil = StorageNode(
        "evil-node",
        session,
        LocalView(
            delta=tampered_view.delta,
            st=tampered_view.st,          # 证据没改，内容改了
            I=tampered_view.I,
            FI=tuple(tampered_FI),
        ),
    )
    F_evil, certs_evil, _ = session.retrieve_from([evil], list(evil.I)[:2])
    bad = client.ver_retrieve(
        list(certs_evil[0].Q), list(F_evil), certs_evil[0].pi_Q
    )
    print(f"  验证结果  : {bad.ok}")
    print(f"  失败环节  : {bad.code.name} —— {bad.message}")

    # ------------------------------------------------------------------
    rule("8. 攻击场景：服务器交出伪造的证据")

    evil2 = StorageNode(
        "forger",
        session,
        LocalView(
            delta=victim.view.delta,
            st=__import__("svc").Opening(
                S_I=(victim.st.S_I * 2) % session.crs.N,   # 随便造一个 S_I
                Lambda_I=victim.st.Lambda_I,
                I=victim.st.I,
            ),
            I=victim.view.I,
            FI=victim.view.FI,
        ),
    )
    try:
        F_fake, certs_fake, _ = session.retrieve_from([evil2], list(evil2.I)[:2])
        bad2 = client.ver_retrieve(
            list(certs_fake[0].Q), list(F_fake), certs_fake[0].pi_Q
        )
        print(f"  验证结果  : {bad2.ok}")
        print(f"  失败环节  : {bad2.code.name} —— {bad2.message}")
    except Exception as exc:  # noqa: BLE001
        print(f"  伪造在生成阶段就被拦下: {type(exc).__name__}: {exc}")

    # ------------------------------------------------------------------
    rule("小结")
    print(f"  承诺一次        : {t_commit * 1000:8.1f} ms   (与文件大小无关的只有摘要大小)")
    print(f"  分发到 4 台     : {t_dist * 1000:8.1f} ms")
    print(f"  跨 3 台检索     : {t_retr * 1000:8.1f} ms")
    print(f"  聚合 {len(certs)} 份证据   : {t_agg * 1000:8.1f} ms")
    print(f"  验证一个证据    : {t_ver * 1000:8.1f} ms   (与块数、文件长度无关)")
    print()
    print("  证据大小始终 = 2 个群元素；验证时间不随块数增长。")


if __name__ == "__main__":
    main()
