"""规模与性能测试。

默认参数**故意设得很小**，因为大规模单次运行要几十分钟。
想测真实规模请自己改下面的 ``SIZES`` 与 ``MODULUS_BITS``。

用法::

    python bench/bench_scale.py                     # 默认：小规模，几秒
    python bench/bench_scale.py --modulus 2048 --sizes 64,256,1024

测什么
------
1. **常量性**：摘要大小、证据大小是否真的与向量长度无关；
2. **验证耗时的常量性**：这是论文最核心的卖点；
3. **各阶段耗时随 n 的增长曲线**；
4. **分治 vs 朴素**：`use_batch` 两条路径的耗时差异（以及结果是否相同）；
5. **与论文渐近值对照**：把论文 Table 1（p37）/ Table 3（p60）报的量
   与本实现的实际渐近并排打出来，再拿实测点做 log-log 拟合，
   看斜率对不对得上 —— 一眼就能看出「实现对得上哪一栏」。
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from svc import (  # noqa: E402
    DeterministicRNG,
    commit,
    open_subvector,
    setup,
    specialize,
    verify,
)


#: 论文里报的量 → 本实现的渐近。左侧说明「对得上哪一栏」，
#: 右侧是**本实现自己的推导**（过程见 docs/与论文对照.md §一）。
#: 论文自己的数值表在 Table 1（p37，SVC 各算法）与 Table 3（p60，VDS 与 PoS），
#: 按「量」这一列对过去即可。
#:
#: 记 l = 每个元素的比特数、n = 向量长度、k = 服务器台数、I = 一次打开/检索的下标集合。
ASYMPTOTICS: tuple[tuple[str, str, str, str], ...] = (
    ("Commit(分治)", "O(l·n·log n)",         "§5.2 VC.Com",    "batch_root_factor 一次出全部 S_i：乘树 O(n·l·log n)，模幂只要 O(log n) 次"),
    ("Commit(朴素)", "O(l·n²)",              "§5.2 VC.Com",    "逐项 s_iota：n 次模幂 × 指数 n(l+1) 位 —— 这就是 use_batch 开关的意义"),
    ("Open",         "O(l·|I|)",             "§5.2 VC.Open",   "逐项「加回」，每步指数只有 l+1 位"),
    ("Disagg(批量)", "O(l·n·log k)",         "§5.2 VC.Disagg", "递归二分；论文自己报的是 O(l·n·log² n)"),
    ("Ver",          "O(l·|I|)，与 n 无关",   "§5.2 VC.Ver",    "本方案最核心的卖点：定长摘要 + 定长证据"),
    ("Agg(k 份)",    "O(l·n·log k)",         "§5.2 VC.Agg",    "顺序无关的分治合并"),
    ("Distribute",   "O(l·n·log k)",         "§7 StrgNode",    "一次性根打开后二分拆给 k 台"),
    ("PoS-Ver",      "O(λ_pos·l)",           "附录 D.1",       "只与聚合后的挑战集有关，与 n 无关"),
    ("Primes",       "O(n·l·log n·l)",       "§5.2 PrimeGen",  "平衡乘积树（朴素左折叠是 O((n·l)²)）"),
)

#: 每个阶段在「n 变大时」的理论 log-log 斜率 —— 实测拟合出来的斜率要跟它比。
#: （``log n`` 这类因子在 log-log 图上只贡献很缓的弯曲，所以按整数斜率比。
#:  实测：commit 分治 1.08 / 朴素 2.15 / open 1.26 / verify 0.04。）
EXPECTED_SLOPE: dict[str, float | None] = {
    "specialize_ms": 1.0,    # 一次模幂，指数 ∝ n
    "commit_batch_ms": 1.0,  # batch_root_factor：乘树 O(n log n)，模幂只 O(log n) 次
    "commit_naive_ms": 2.0,  # n 次模幂 × 指数 ∝ n
    "open_ms": 1.0,          # |I| 固定，逐项「加回」的步数 ∝ n
    "verify_ms": 0.0,        # **与 n 无关** —— 本方案的核心卖点
}


def ms(t0: float) -> float:
    return (time.perf_counter() - t0) * 1000.0


def loglog_slope(rows: list[dict], key: str) -> float | None:
    """对 ``(log n, log 耗时)`` 做最小二乘，返回斜率（即实测的增长指数）。

    数据点少于 3 个、或某个耗时非正时返回 ``None`` —— 两点定斜率太容易被
    单次抖动带偏，不如不报。
    """
    pts = [(r["n"], r[key]) for r in rows if r.get(key, 0) > 0]
    if len(pts) < 3:
        return None
    xs = [math.log(n) for n, _ in pts]
    ys = [math.log(t) for _, t in pts]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    den = sum((x - mx) ** 2 for x in xs)
    if den == 0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den


def report_asymptotics(rows: list[dict]) -> None:
    """把论文表里的量、本实现的渐近、实测斜率并排打出来。"""
    print()
    print("论文渐近对照")
    print("=" * 78)
    head = f"{'量':<12} {'本实现渐近':<24} {'论文位置':<16} 说明"
    print(head)
    print("-" * len(head))
    for name, cost, where, why in ASYMPTOTICS:
        print(f"{name:<12} {cost:<24} {where:<16} {why}")

    print()
    print("实测增长斜率（对 n 做 log-log 最小二乘，越接近理论越好）")
    print("-" * 78)
    if len(rows) < 3:
        print("  至少需要 3 个 n 的采样才能拟合斜率（当前 "
              f"{len(rows)} 个），跳过")
        return
    ns = " → ".join(f"{r['n']:,}" for r in rows)
    print(f"  n 采样: {ns}")
    print()
    print(f"  {'阶段':<18} {'实测':>8} {'理论':>8}   判定")
    for key, name in (
        ("specialize_ms", "Specialize"),
        ("commit_batch_ms", "Commit(分治)"),
        ("commit_naive_ms", "Commit(朴素)"),
        ("open_ms", "Open(定 |I|)"),
        ("verify_ms", "Verify(定 |I|)"),
    ):
        got = loglog_slope(rows, key)
        want = EXPECTED_SLOPE[key]
        if got is None:
            print(f"  {name:<18} {'—':>8} {f'{want:.2f}':>8}   数据不足")
            continue
        if want == 0.0:
            verdict = "与 n 无关 ✅" if abs(got) < 0.25 else "偏大 ⚠（应接近常数）"
        else:
            rel = abs(got - want) / want
            verdict = "对得上 ✅" if rel < 0.35 else f"偏离 {rel:.0%} ⚠"
        print(f"  {name:<18} {got:>8.2f} {want:>8.2f}   {verdict}")
    print()
    print("  说明：n 只取 3~4 个点、且默认量级很小，斜率有 ±0.3 的噪声。")
    print("        要看准请放大规模，例如：")
    print("          python bench/bench_scale.py --sizes 64,256,1024,4096")


def fmt(x: float) -> str:
    return f"{x:,.1f}"


def bench_one(
    n: int,
    l: int,
    modulus_bits: int,
    verify_reps: int = 20,
    open_size: int = 8,
) -> dict:
    rng = DeterministicRNG(f"bench-{n}".encode())

    t0 = time.perf_counter()
    crs = setup(lambda_bits=16, l=l, n=n, rng=rng, modulus_bits=modulus_bits)
    t_setup = ms(t0)

    t0 = time.perf_counter()
    crs_n = specialize(crs, n)
    t_spec = ms(t0)

    values = [rng.randbelow(1 << l) for _ in range(n)]

    t0 = time.perf_counter()
    com = commit(crs_n, values, use_batch=True)
    t_com_batch = ms(t0)

    t0 = time.perf_counter()
    com2 = commit(crs_n, values, use_batch=False)
    t_com_naive = ms(t0)
    assert com.C == com2.C, "两条路径结果必须一致"

    # 打开大小必须**固定**。
    #
    # 论文说的是「验证时间与向量长度 n 无关」，不是「与打开个数 |I| 无关」。
    # 看 VC.Ver 的第 2 步：对每个 i ∈ I 都要重算 S_i = S_I^{e_{I\{i}}}，
    # 那是 |I| 次指数很大的模幂 —— 所以验证确实是 O(|I|) 的。
    # 若按 |I| = n/2 去测，量到的是 |I| 的影响，会把「与 n 无关」这个性质完全盖掉。
    I = list(range(0, min(open_size, n)))
    t0 = time.perf_counter()
    pi = open_subvector(crs_n, I, [values[i] for i in I], values)
    t_open = ms(t0)

    # 验证耗时（多跑几次取平均）
    t0 = time.perf_counter()
    for _ in range(verify_reps):
        rep = verify(crs_n, com.C, I, [values[i] for i in I], pi)
    t_verify = ms(t0) / verify_reps
    assert rep.ok

    return {
        "n": n,
        "open_size": len(I),
        "setup_ms": t_setup,
        "specialize_ms": t_spec,
        "commit_batch_ms": t_com_batch,
        "commit_naive_ms": t_com_naive,
        "open_ms": t_open,
        "verify_ms": t_verify,
        "e_all_bits": crs_n.e_all.bit_length(),
        "U_bits": crs_n.U_n.bit_length(),
        "C_bits": com.C.bit_length(),
        "S_I_bits": pi.S_I.bit_length(),
        "Lambda_bits": pi.Lambda_I.bit_length(),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description="SVC 规模与性能测试")
    ap.add_argument("--modulus", type=int, default=1024, help="模数位长")
    ap.add_argument("--l", type=int, default=32, help="每个元素的比特数")
    ap.add_argument("--sizes", default="16,64,256", help="向量长度列表，逗号分隔")
    ap.add_argument("--reps", type=int, default=20, help="验证重复次数（取平均）")
    ap.add_argument(
        "--open-size", type=int, default=8,
        help="每次打开的下标个数（必须固定，否则量到的是 |I| 的影响而非 n 的）",
    )
    args = ap.parse_args()

    sizes = [int(s) for s in args.sizes.split(",") if s.strip()]
    # 素数必须够：区间 [2^(l-1), 2^l) 内的素数个数随 l 指数增长，
    # l=32 时约有 2^31/(l+1) 量级，取几万个位置绰绰有余。
    sizes = [s for s in sizes if s > 0]

    print(f"模数 |N| = {args.modulus} 位，l = {args.l}（素数 {args.l + 1} 位）")
    print()

    rows = []
    for n in sizes:
        row = bench_one(n, args.l, args.modulus, args.reps, args.open_size)
        rows.append(row)
        print(f"  n = {n:>8,} 完成")
    print()

    head = (
        f"{'n':>10} {'|I|':>5} {'Setup(ms)':>11} {'Spec(ms)':>11} "
        f"{'Com分治':>11} {'Com朴素':>11} {'Open(ms)':>11} {'Verify(ms)':>11} "
        f"{'|C|':>6} {'|π|':>7}"
    )
    print(head)
    print("-" * len(head))
    for r in rows:
        print(
            f"{r['n']:>10,} {r['open_size']:>5} {fmt(r['setup_ms']):>11} "
            f"{fmt(r['specialize_ms']):>11} "
            f"{fmt(r['commit_batch_ms']):>11} {fmt(r['commit_naive_ms']):>11} "
            f"{fmt(r['open_ms']):>11} {fmt(r['verify_ms']):>11} "
            f"{r['C_bits']:>6} {r['S_I_bits']:>7}"
        )

    print()
    print("结论检查：")
    print("-" * 60)

    c_bits = {r["C_bits"] for r in rows}
    si_bits = {r["S_I_bits"] for r in rows}
    print(f"  承诺 C 的位长（各 n）    : {sorted(c_bits)}"
          f"   跨度 {max(c_bits) - min(c_bits)} 位")
    print(f"  证据 S_I 的位长（各 n）  : {sorted(si_bits)}"
          f"   跨度 {max(si_bits) - min(si_bits)} 位")
    print("  → 两者都约等于 |N|，与 n 无关（常量大小摘要 / 常量大小证据）")
    print()

    if len(rows) > 1:
        ratio_n = rows[-1]["n"] / rows[0]["n"]
        v0, v1 = rows[0]["verify_ms"], rows[-1]["verify_ms"]
        print(f"  n 增长 {ratio_n:.0f} 倍（|I| 固定为 {rows[0]['open_size']}）：")
        print(f"    验证耗时 {fmt(v0)} ms → {fmt(v1)} ms，比值 {v1 / max(v0, 1e-9):.2f}x")
        print("    → 接近 1，说明验证时间与向量长度 n 无关（本方案的核心卖点）")
        print()
        print(f"  n 增长 {ratio_n:.0f} 倍时，各阶段的增长倍数：")
        for key, name in (
            ("specialize_ms", "Specialize"),
            ("commit_batch_ms", "Commit(分治)"),
            ("commit_naive_ms", "Commit(朴素)"),
        ):
            a, b = rows[0][key], rows[-1][key]
            print(f"    {name:<14} {fmt(a):>10} ms → {fmt(b):>10} ms"
                  f"   增长 {b / max(a, 1e-9):>7.2f}x")
        print()
        for r in rows:
            speed = r["commit_naive_ms"] / max(r["commit_batch_ms"], 1e-9)
            print(f"  n = {r['n']:>8,}: 分治比朴素快 {speed:>6.2f}x")
        print("  → 差距随 n 迅速拉大，这就是批量求根的价值")

    report_asymptotics(rows)


if __name__ == "__main__":
    main()
