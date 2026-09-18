r"""第二个 SVC 方案本体 —— 对应 to-do-function-list.txt 第三、四、五部分（#12~#26）。

论文出处：ASIACRYPT 2020,
*Incrementally Aggregatable Vector Commitments and Applications to Verifiable
Decentralized Storage*, **§5.2 Our Second SVC Construction**。

记号（全部照抄论文 §5.2，一个符号都不要改）
--------------------------------------------
=================  ====================================================
符号                含义
=================  ====================================================
:math:`e_i`        第 ``i`` 个 ``(l+1)`` 比特素数
:math:`e_I`        :math:`\\prod_{i \\in I} e_i`
:math:`e_{[n]}`    :math:`\\prod_{i=1}^{n} e_i`，记作 ``e_all``
:math:`S_i`        :math:`g^{e_{[n]} / e_i}`
:math:`S_I`        :math:`g^{e_{[n]} / e_I} = U_n^{1/e_I}`
:math:`U_n`        :math:`g^{e_{[n]}}`
:math:`C`          :math:`\\prod_{i=1}^{n} S_i^{v_i}`
:math:`\\Lambda_I`  :math:`\\left(\\prod_{j \\notin I} S_j^{y_j}\\right)^{1/e_I}`
=================  ====================================================

论文算法（§5.2 原文）
----------------------
::

    VC.Setup(1^λ, ℓ, n) → crs
    VC.Specialize(crs, n) → crs_n        计算 e_i = PrimeGen(i)，U_n = g^{e_[n]}
    VC.Com(crs, v⃗) → (C, aux)            S_i = g^{e_[n]\{i}}，C = ∏ S_i^{v_i}
    VC.Open(crs, I, y⃗, aux) → π_I
        S_j^{1/e_I} ← g^{e_[n]\(I∪{j})}   （j ∉ I）
        S_I ← g^{e_[n]\I}
        Λ_I ← ∏_{j∉I} (S_j^{1/e_I})^{y_j}
        π_I := (S_I, Λ_I)
    VC.Ver(crs, C, I, y⃗, π_I) → b
        S_i = S_I^{e_{I\{i}}} = U_n^{1/e_i}   对每个 i ∈ I
        接受 ⟺  S_I^{e_I} = U_n  ∧  C = Λ_I^{e_I} · ∏_{i∈I} S_i^{y_i}
    VC.Disagg(crs, I, v⃗_I, π_I, K) → π_K        （K ⊆ I）
        S_K ← S_I^{e_{I\K}}
        χ_j = S_K^{1/e_j} ← S_I^{e_{I\(K∪{j})}}   对每个 j ∈ I\K
        Λ_K ← Λ_I^{e_{I\K}} · ∏_{j∈I\K} χ_j^{v_j}
    VC.Agg(crs, (I,v⃗_I,π_I), (J,v⃗_J,π_J)) → π_K     （K = I ∪ J，I ∩ J = ∅）
        S_K ← ShamirTrick(S_I, S_J, e_I, e_J)
        φ_j ← S_K^{e_{J\{j}}}   (j ∈ J)    ψ_i ← S_K^{e_{I\{i}}}   (i ∈ I)
        ρ_I ← Λ_I / ∏_{j∈J} φ_j^{v_j}
        σ_J ← Λ_J / ∏_{i∈I} ψ_i^{v_i}
        Λ_K ← ShamirTrick(ρ_I, σ_J, e_I, e_J)

实现上的两个关键加速（都不改变结果，只改代价）
------------------------------------------------
1. **``S_i`` 一次全算**：用 :func:`~svc.mathbase.batch_root_factor_any`
   （分治批量求根），而不是对每个 ``i`` 单独 ``pow(g, e_all // e_i, N)``。
   后者每个指数都有 ``(n-1)(l+1)`` 位，``n`` 次这种模幂完全不可用。

2. **``Λ`` 的「摊开」写法**：:math:`\\Lambda_I` 定义里那个整体 ``1/e_I`` 次方
   **不能真去开方**（那正是 RSA 假设）。做法是把 ``1/e_I`` 摊到每一项上：

   .. math::
      \\Lambda_I = \\prod_{j \\notin I} \\left(g^{\\,e_{[n]}/(e_j e_I)}\\right)^{y_j}

   每一项的指数都是**整数**，于是变成 :func:`~svc.mathbase.weighted_root_product`：
   先用一次分治拿到 :math:`\\{g^{E/e_j}\\}`（``E = e_{[n]}/e_I``），
   再用 ``y_j`` 这个 ``l`` 位小指数加权相乘。
   清单 #15 的 PS 说的「先算 ``S_j`` 的 ``1/e_I`` 次方，再乘方 ``v_i``」就是这一步。
"""

from __future__ import annotations

from typing import Iterable, Sequence

from .groups import MIN_MODULUS_BITS, generate_primes
from .mathbase import (
    batch_root_factor_any,
    batch_root_factor_general,
    group_div,
    product_tree,
    shamir_trick,
    weighted_root_product,
)
from .primegen import PrimeGen, PrimeGenHash
from .rng import DeterministicRNG
from .types import (
    CRS,
    CRSn,
    Commitment,
    Opening,
    VectorDigest,
    VerifyCode,
    VerifyReport,
    as_index_set,
)

__all__ = [
    # 核心抽象
    "VectorDigest",
    "digest_of",
    "add_back",
    # 中间量
    "e_of",
    "s_iota",
    "s_subset",
    "s_partial_root",
    "reconstruct_s_i",
    "lambda_subset",
    "multi_exponentiate",
    # 本体
    "setup",
    "specialize",
    "commit",
    "open_subvector",
    "verify",
    "disagg",
    "agg",
    "disagg_one_to_many",
    "agg_many_to_one",
    # 常量
    "DEFAULT_MODULUS_BITS",
]


#: 默认模数位长。论文的实验配置就是 ``|N| = 2048``、``λ = 128``、``ℓ = 128``。
#: 注意 ``λ`` 在这里主要影响素映射的选择，真正决定 RSA 安全强度的是 ``|N|``。
DEFAULT_MODULUS_BITS: int = 2048


# ===========================================================================
# 三、方案中间量（清单 #12 ~ #17）
# ===========================================================================

def e_of(primegen: PrimeGen | PrimeGenHash, I: Iterable[int]) -> int:
    """计算 :math:`e_I = \\prod_{i \\in I} e_i`。对应清单 **#12**。

    清单原文要求「另外要单独保存 ``e_all = e_of(全部下标)``，后面几乎每个
    函数都要用」—— ``e_all`` 保存在 :class:`~svc.types.CRSn` 的 ``e_all`` 字段里。

    用 :func:`~svc.mathbase.product_tree` 而非顺序连乘：``I`` 很大时
    （``n = 2^16``）顺序连乘是 :math:`O(n^2)`，树形是 :math:`O(n \\log n)`。

    :param I: 下标集合。空集合返回 1（空乘积，符合 :math:`e_\\varnothing = 1`）。
    """
    indices = list(I)
    if not indices:
        return 1
    return product_tree([primegen.get(int(i)) for i in indices])


def s_iota(g: int, e_all: int, e_i: int, N: int) -> int:
    """计算 :math:`S_i = g^{e_{[n]}/e_i}`。对应清单 **#13**。

    «因为 ``e_i`` 整除 ``e_{[n]}``，所以是整数除法加普通模幂，不需要求根。»
    —— 这句话是整个方案能「公开计算见证」的基石：
    我们不知道群的阶，但**不需要**知道，因为指数是整数。

    :raises ValueError: ``e_i`` 不整除 ``e_all``（说明下标越界或素数映射不一致）。
    """
    if e_all % e_i != 0:
        raise ValueError(
            f"e_i 不整除 e_all（e_all % e_i = {e_all % e_i}）："
            f"下标越界，或素数映射与 specialize 用的不是同一个"
        )
    return pow(g, e_all // e_i, N)


def s_subset(g: int, e_all: int, e_I: int, N: int) -> int:
    """计算 :math:`S_I = g^{e_{[n]}/e_I}`。对应清单 **#14**。

    «它是最关键的中间量之一，占打开证明的一半» —— :math:`\\pi_I` 的第一个分量。

    论文里 :math:`S_I = U_n^{1/e_I}`：定义上是一个 ``e_I`` 次根，
    但因为 :math:`e_I \\mid e_{[n]}`，指数 :math:`e_{[n]}/e_I` 是整数，
    于是不需要开方，直接模幂即可。
    """
    if e_I == 0:
        raise ValueError("e_I 不能为 0")
    if e_all % e_I != 0:
        raise ValueError(
            f"e_I 不整除 e_all：说明 I 里有下标超出了 specialize 时用的 n"
        )
    return pow(g, e_all // e_I, N)


def s_partial_root(g: int, e_all: int, e_I: int, e_j: int, N: int) -> int:
    """计算 :math:`S_j^{1/e_I} = g^{e_{[n]}/(e_j e_I)}`。对应清单 **#15**。

    **要求 ``j ∉ I``**。这正是「``1/e_I`` 次方为什么能公开算」的具体体现：
    两个下标集合不相交 ⇒ :math:`e_j \\cdot e_I \\mid e_{[n]}` ⇒ 指数是整数
    ⇒ 直接模幂，不需要求根。

    反过来说，若 ``j ∈ I``，:math:`e_j^2` 就未必整除 :math:`e_{[n]}` 了
    （:math:`e_{[n]}` 里每个 :math:`e_i` 只出现一次），此时**求不出来**。

    :raises ValueError: ``e_j * e_I`` 不整除 ``e_all``（即 ``j ∈ I`` 或下标越界）。
    """
    divisor = e_j * e_I
    if e_all % divisor != 0:
        raise ValueError(
            f"e_j * e_I 不整除 e_all：j 可能落在 I 里（这时代数是求不出根的），"
            f"或下标越界"
        )
    return pow(g, e_all // divisor, N)


def reconstruct_s_i(
    S_I: int,
    I: Sequence[int],
    i: int,
    primegen: PrimeGen | PrimeGenHash,
    N: int,
) -> int:
    """由 :math:`S_I` 重构 :math:`S_i = S_I^{e_{I \\setminus \\{i\\}}}`。对应清单 **#16**。

    验证方**必须**先做这一步：清单原文「因为 ``S_i`` 不在公开参数里，
    验证者只能从 ``S_I`` 现场重构出来」。

    往深一层看，:math:`S_I^{e_{I\\setminus\\{i\\}}} = g^{e_{[n]}/e_I \\cdot e_{I\\setminus\\{i\\}}}
    = g^{e_{[n]}/e_i} = S_i`，与 :math:`S_i` 的定义完全吻合 ——
    这也顺带说明「公开参数里不需要存 :math:`S_1,\\dots,S_n`」，
    这正是相比 CF13 原方案把参数从线性降到常数的关键一步。

    :raises ValueError: ``i`` 不在 ``I`` 里。
    """
    I_set = as_index_set(I)
    if i not in I_set:
        raise ValueError(f"下标 {i} 不在集合 I 里，无法重构 S_i")
    e_I_minus_i = e_of(primegen, [j for j in I_set if j != i])
    return pow(S_I, e_I_minus_i, N)


def lambda_subset(
    g: int,
    e_all: int,
    I: Sequence[int],
    vals: Sequence[int],
    N: int,
    primegen: PrimeGen | PrimeGenHash,
    n: int | None = None,
    *,
    use_batch: bool = True,
) -> int:
    """计算 :math:`\\Lambda_I = \\left(\\prod_{j \\notin I} S_j^{y_j}\\right)^{1/e_I}`。对应清单 **#17**。

    :param vals: **整个向量**的值（``y_1, ..., y_n``）。
                 :math:`\\Lambda_I` 的指数里要用到**所有** ``j ∉ I`` 的值，
                 不只是 ``I`` 里的，所以这里必须传全量。
    :param primegen: 需要它来取 :math:`e_j`
    :param n: 向量长度；``None`` 表示取 ``len(vals)``
    :param use_batch: ``True`` 走分治批量求根（快）；``False`` 逐项 :func:`s_partial_root`（慢但好调试）

    «注意不能写成「先乘起来再开 e_I 次方」» —— 群元素的 :math:`e_I` 次根
    求不出来。正确写法是把 ``1/e_I`` 摊进每一项的指数（见模块 docstring）。

    ``I = [n]`` 时全体下标都在集合里，``∏`` 为空，按空乘积定义 :math:`\\Lambda_{[n]} = 1`。
    """
    n = len(vals) if n is None else n
    I_set = set(int(i) for i in I)

    outside = [j for j in range(n) if j not in I_set]
    if not outside:
        return 1  # 空乘积

    if use_batch:
        # 一条路走到黑：分治拿到 {g^{E/e_j}}，再按 y_j 加权相乘
        return weighted_root_product(
            g,
            [vals[j] for j in outside],
            [primegen.get(j) for j in outside],
            N,
        )

    # 朴素路径：逐项 s_partial_root。慢 O(|outside|) 次大指数模幂，
    # 但每一步都能单独打印检查，debug 时用这条。
    e_I = e_of(primegen, I_set)
    acc = 1
    for j in outside:
        t = s_partial_root(g, e_all, e_I, primegen.get(j), N)
        y = vals[j]
        if y:
            acc = acc * pow(t, y, N) % N
    return acc


# ===========================================================================
# 核心抽象：向量摘要 d(v \ I) = (S, Λ)
# ===========================================================================
#
# 这一层把「承诺」「打开」「拆分」「追加」全部收到同一个概念底下：
#
#     承诺 = digest_of(crs_n, v, excluded=∅)       →  (U_n, C)
#     打开 = digest_of(crs_n, v, excluded=I)       →  (S_I, Λ_I)
#     拆分 = 从 d(v\I) 出发，把 I\K 逐个「加回去」   →  d(v\K)
#
# 之所以能统一，是因为**子向量打开证明本来就定义为「去掉 I 之后那个向量的摘要」**。

def digest_of(
    crs_n: CRSn,
    vals: Sequence[int],
    excluded: Sequence[int] = (),
    *,
    use_batch: bool = True,
) -> VectorDigest:
    """计算 :math:`d(\\mathbf{v} \\setminus I) = (S_I, \\Lambda_I)`。

    :param vals: **整个向量**的值（不是子向量的）
    :param excluded: 要去掉的下标集合 ``I``
    :param use_batch: ``True`` 走分治批量求根；``False`` 逐项（慢但好调试）

    两个特例就是方案里的两个基本操作：

    * ``excluded = ()`` → :math:`(U_n, C)`，即**承诺**
    * ``excluded = I`  → :math:`(S_I, \\Lambda_I)`，即**打开证明**

    实现上直接复用清单里的 ``s_subset`` + ``lambda_subset``，不重复造轮子。
    """
    if len(vals) != crs_n.n:
        raise ValueError(
            f"向量长度 {len(vals)} 与 specialize 的 n = {crs_n.n} 不一致"
        )
    primegen = crs_n.crs.primegen
    I_set = set(int(i) for i in excluded)

    e_I = e_of(primegen, I_set)
    S = s_subset(crs_n.g, crs_n.e_all, e_I, crs_n.N)
    Lambda = lambda_subset(
        crs_n.g, crs_n.e_all, I_set, vals, crs_n.N, primegen, crs_n.n,
        use_batch=use_batch,
    )
    return VectorDigest(S, Lambda)


def add_back(S: int, Lambda: int, e_i: int, v_i: int, N: int) -> tuple[int, int]:
    """把一个位置「加回」摘要 —— 整个重构的支点。

    设当前摘要为 :math:`d(\\mathbf{v} \\setminus I)`，其中 ``i ∈ I``。
    把位置 ``i`` 加回去，就得到 :math:`d(\\mathbf{v} \\setminus (I \\setminus \\{i\\}))`：

    .. math::
        S' = S^{e_i}, \\qquad \\Lambda' = \\Lambda^{e_i} \\cdot S^{v_i}

    注意 :math:`S^{v_i}` 用的是**更新前**的 ``S``。

    正确性（``i ∉ [n]\\setminus I``，所以新摘要要多含一个位置 ``i``）:

    .. math::
        S' = g^{\\,(e_{[n]}/e_I)\\cdot e_i}
           = g^{\\,e_{[n]}/e_{I\\setminus\\{i\\}}} \\quad\\checkmark

    .. math::
        \\Lambda' = \\!\\!\\!\\!\\prod_{j \\in [n]\\setminus(I\\setminus\\{i\\})}\\!\\!\\!
                     (S'^{1/e_j})^{v_j}
                  = \\Lambda^{e_i} \\cdot (S'^{1/e_i})^{v_i}
                  = \\Lambda^{e_i} \\cdot S^{v_i} \\quad\\checkmark

    代价 :math:`O(\\ell)` 次群运算（两个 ``(ℓ+1)`` 位指数 + 一个 ``ℓ`` 位指数）。

    一件事归约成三步：**拆分**（:func:`disagg`）、**验证**（:func:`verify`）、
    **追加新位置**（CF 方案的向量扩展）都只是把它循环调用若干次。
    """
    return pow(S, e_i, N), (pow(Lambda, e_i, N) * pow(S, v_i, N)) % N


def multi_exponentiate(pairs: Iterable[tuple[int, int]], N: int) -> int:
    """计算 :math:`\\prod (base^{exp}) \\bmod N`（多项同时幂）。

    :param pairs: ``(base, exponent)`` 序列

    清单 #22 说「第二步的乘积用 multiexp 算」。这里说明一下为什么**没有**
    用 :func:`~svc.mathbase.multiexp`：那个函数的语义是
    :math:`\\prod a_i^{X/x_i}`（需要知道全部 ``x_i`` 之积 ``X``），
    而这里要算的是 :math:`\\prod S_i^{y_i}` —— 指数 ``y_i`` 是**独立的小整数**
    （``l`` 位），不构成 ``X/x_i`` 的形式。

    对这种「指数都很小」的情形，逐项模幂本来就是最优解：
    ``n`` 次 ``l`` 位指数的模幂，代价 :math:`O(n \\cdot l)` 次模乘。
    真正的 :func:`~svc.mathbase.multiexp` 用在 :func:`lambda_subset` 那条路上，
    那里才有 :math:`1/e_I` 需要摊开。
    """
    acc = 1
    for base, exponent in pairs:
        if exponent:
            acc = acc * pow(base, exponent, N) % N
    return acc


# ===========================================================================
# 四、方案本体（清单 #18 ~ #24）
# ===========================================================================

def setup(
    lambda_bits: int,
    l: int,
    n: int,
    rng: DeterministicRNG | None = None,
    *,
    modulus_bits: int | None = None,
    primegen_cls: type = PrimeGen,
) -> CRS:
    """``VC.Setup`` —— 生成 CRS。对应清单 **#18**。

    :param lambda_bits: 安全参数 :math:`\\lambda`
    :param l: 每个元素的比特数 ``l``；素数位长为 ``l + 1``
    :param n: 向量长度
    :param rng: 随机源，``None`` 用默认种子（便于复现）
    :param modulus_bits: 模数位长。``None`` 时取 ``16·λ``（λ=128 → 2048 位，
                         与论文实验配置一致）
    :param primegen_cls: 素数映射类型，默认双射版 :class:`~svc.primegen.PrimeGen`。
                         传 :class:`~svc.primegen.PrimeGenHash` 可切到哈希版对照。
    :returns: :class:`~svc.types.CRS` = ``(N, g, primegen, l)``

    .. note::

       **``Setup`` 不含 ``U_n``**。`U_n` 依赖向量长度 ``n``，属于
       ``Specialize`` 阶段。这个拆分在 VDS 里很关键：见论文 §8.2 ——
       ``U`` 会随文件增删变化，所以必须挂在摘要 ``δ`` 上而不是 ``pp`` 里。
    """
    if lambda_bits <= 0:
        raise ValueError("lambda_bits 必须为正")
    if l <= 0:
        raise ValueError("l 必须为正")
    if n <= 0:
        raise ValueError("n 必须为正")

    if modulus_bits is None:
        modulus_bits = max(MIN_MODULUS_BITS, 16 * lambda_bits)

    if rng is None:
        rng = DeterministicRNG(b"svc-v1-setup")

    N, g = generate_primes(rng, modulus_bits)
    primegen = primegen_cls(max_sz=n, bits=l + 1)
    return CRS(N=N, g=g, primegen=primegen, l=l)


def specialize(crs: CRS, n: int) -> CRSn:
    """``VC.Specialize`` —— 计算素数、累加全体位置。对应清单 **#19**。

    .. math::
        e_1, \\dots, e_n \\leftarrow \\text{PrimeGen}(i), \\qquad U_n = g^{e_{[n]}}

    :returns: :class:`~svc.types.CRSn` = ``(crs, U_n, e_all, n)``

    清单特别强调「要把 ``e_all`` 一起存下来，后面每个算法都要用」：
    :func:`s_subset`、:func:`s_partial_root`、:func:`lambda_subset` 全都要它。

    代价提示：``U_n`` 是一次指数位长为 :math:`n(l+1)` 的模幂。
    ``n = 2^{16}``、``l+1 = 129`` 时指数有 840 万位，
    在 CPython 下就是**数十秒**——这是整个方案最贵的一步，
    但每个文件只需做一次（而且 VDS 里可以增量更新，见 :mod:`vds`）。
    """
    if n != crs.primegen.max_sz:
        # 允许更小的 n（例如只对前 n 个位置做专门化），但不能超过映射容量
        if n > crs.primegen.max_sz:
            raise ValueError(
                f"要求 n = {n}，但素数映射只准备了 {crs.primegen.max_sz} 个"
            )

    e_list = crs.primegen.first(n)
    e_all = product_tree(e_list)
    U_n = pow(crs.g, e_all, crs.N)
    return CRSn(crs=crs, U_n=U_n, e_all=e_all, n=n)


def commit(
    crs_n: CRSn,
    vals: Sequence[int],
    *,
    use_batch: bool = True,
) -> Commitment:
    """``VC.Com`` —— 承诺。对应清单 **#20**。

    三步（清单原文）：

    1. 算出全部 :math:`S_i`；
    2. :math:`C = \\prod_i S_i^{v_i}`；
    3. ``aux = vals``（就是原始数据本身）。

    :param use_batch: ``True`` 用 :func:`~svc.mathbase.batch_root_factor_any`
                      一次算出所有 :math:`S_i`；``False`` 逐项 :func:`s_iota`。
                      清单 PS 说「前期使用 13 进行 debug，这里的 8 算大量内容更快，
                      但是出错不好修」—— 就是这个开关。

    :returns: :class:`~svc.types.Commitment`，其中 ``C`` 是**单个群元素，
              与向量长度无关**（succinct 的核心指标）。
    """
    n = len(vals)
    if n != crs_n.n:
        raise ValueError(f"向量长度 {n} 与 specialize 的 n = {crs_n.n} 不一致")

    e_list = crs_n.crs.primegen.first(n)

    if use_batch:
        S = batch_root_factor_any(crs_n.g, e_list, crs_n.N)
    else:
        S = [s_iota(crs_n.g, crs_n.e_all, e, crs_n.N) for e in e_list]

    # C = ∏ S_i^{v_i}
    C = multi_exponentiate(zip(S, vals), crs_n.N)
    return Commitment(C=C, aux=tuple(int(v) for v in vals))


def open_subvector(
    crs_n: CRSn,
    I: Sequence[int],
    vals_I: Sequence[int],
    aux: Sequence[int],
    *,
    use_batch: bool = True,
) -> Opening:
    """``VC.Open`` —— 生成子向量打开证明。对应清单 **#21**。

    .. math::
        S_I = g^{e_{[n]}/e_I}, \\qquad
        \\Lambda_I = \\prod_{j \\notin I} \\left(S_j^{1/e_I}\\right)^{y_j}

    :param I: 要打开的下标集合
    :param vals_I: 声明这些下标的值（会与 ``aux`` 交叉校验）
    :param aux: **整个向量**的值。:math:`\\Lambda_I` 里 ``j ∉ I`` 那部分的指数
                要用到它们，所以必须传全量，不能只传 ``vals_I``。
    :returns: :class:`~svc.types.Opening` —— **两个群元素，与向量长度和打开个数都无关**。
    """
    raw = list(I)
    if len(set(raw)) != len(raw):
        raise ValueError("I 里有重复下标")
    if len(vals_I) != len(raw):
        raise ValueError("vals_I 的长度与 I 不一致")

    # 把 (下标, 值) **成对**排序：这样 vals_I 里第 k 个值就对应 I 里第 k 个下标，
    # 调用方传 [9, 1, 4] 及其对应的三个值也没问题。
    # 反之若像先前那样先排序 I、再按排序后的 I 去索引原来的 vals_I，
    # 会把值安到错的下标上。
    pairs = sorted(zip(raw, vals_I))
    I_set = tuple(i for i, _ in pairs)

    if I_set and (I_set[0] < 0 or I_set[-1] >= crs_n.n):
        raise ValueError(f"I 里有下标越界（合法范围 0..{crs_n.n - 1}）")

    # 交叉校验：声明的值与原始数据必须一致
    for idx, value in pairs:
        if aux[idx] != value:
            raise ValueError(
                f"下标 {idx} 的声明值 {value} 与 aux 里的 {aux[idx]} 不符"
            )

    # π_I = d(v \ I) —— 就是这个统一抽象的取值
    d = digest_of(crs_n, aux, I_set, use_batch=use_batch)
    return Opening.from_digest(d, I_set)


def verify(
    crs_n: CRSn,
    C: int,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening,
) -> VerifyReport:
    """``VC.Ver`` —— 验证。对应清单 **#22**。

    论文原文（§5.2）::

        对每个 i ∈ I 计算 S_i = S_I^{e_{I\\{i}}} = U_n^{1/e_i}
        接受 ⟺  S_I^{e_I} = U_n  ∧  C = Λ_I^{e_I} · ∏_{i∈I} S_i^{y_i}

    清单把过程拆成三步，并要求「具体哪一步非真可以返回不同的警告」：
    本函数返回 :class:`~svc.types.VerifyReport`，``.code`` 就是失败环节，
    可以直接给前端展示。

    第 1 步为什么必要：验证方没有 :math:`S_1,\\dots,S_n`，
    :math:`S_i` 是从 :math:`S_I` 现场重构的。如果不对 :math:`S_I` 做校验，
    恶意方可以挑一个任意的 :math:`S_I` 让第 3 步凑巧成立。
    而第 1 步只用**一次模幂** :math:`S_I^{e_I} = U_n`，
    就把 :math:`S_I` 锁死为 :math:`g^{e_{[n]}/e_I}` 那一项。

    第 2 步用 :func:`reconstruct_s_i`；第 3 步的乘积走 :func:`multi_exponentiate`。
    """
    I_set = as_index_set(I)

    # ---- 形状检查 ----
    if len(I_set) != len(list(I)):
        return VerifyReport.fail(VerifyCode.BAD_SHAPE, "I 里有重复下标")
    if len(vals_I) != len(I_set):
        return VerifyReport.fail(
            VerifyCode.BAD_SHAPE, "vals_I 的长度与 I 不一致"
        )
    if I_set and (I_set[0] < 0 or I_set[-1] >= crs_n.n):
        return VerifyReport.fail(
            VerifyCode.BAD_SHAPE, f"I 里有下标越界（合法范围 0..{crs_n.n - 1}）"
        )
    if pi_I.I and pi_I.I != I_set:
        return VerifyReport.fail(
            VerifyCode.BAD_SHAPE,
            f"证明里的下标 {list(pi_I.I)} 与传入的 I {list(I_set)} 不一致",
        )

    primegen = crs_n.crs.primegen
    N = crs_n.N

    # ---- 顺序把 I 里每个位置「加回」摘要 ----
    #
    # 视角：pi_I = d(v \ I)。把 I 里每个位置逐个加回去，最终必须变回
    # d(v) = (U_n, C)。每一步都是 :func:`add_back`，代价 O(ℓ)。
    #
    # 这与论文「先算 S_i = S_I^{e_{I\{i}}} 再乘起来」在代数上**完全等价**，
    # 但代价从 O(ℓ|I|²) 降到 O(ℓ|I|)：
    # 论文写法里每次重构 S_i 的指数都有 (|I|-1)(ℓ+1) 位，|I| 次就是平方级；
    # 这里每次的指数只有 (ℓ+1) 位，总代价线性。
    #
    # 代价优势在大 |I| 时非常明显（|I| = 512 时相差三个数量级）。
    S, Lam = pi_I.S_I, pi_I.Lambda_I
    for i, v_i in zip(I_set, vals_I):
        S, Lam = add_back(S, Lam, primegen.get(i), int(v_i), N)

    # 第 1 步检查（S 那条）与第 3 步检查（Λ 那条）自然分开：
    # 加回过程中 S 只依赖 pi_I.S_I 与素数，完全不看 Λ；
    # 而 Λ 的演化依赖中间每一步的 S。
    if S != crs_n.U_n:
        return VerifyReport.fail(
            VerifyCode.BAD_S_I,
            "S_I 校验失败：S_I^{e_I} ≠ U_n，S_I 被伪造或下标集合不对",
        )

    if Lam != C % N:
        return VerifyReport.fail(
            VerifyCode.BAD_LAMBDA,
            "Λ_I 校验失败：Λ_I^{e_I} · ∏_{i∈I} S_i^{y_i} ≠ C，"
            "要么数据被改过，要么 Λ_I 不对",
        )

    return VerifyReport.success()


def disagg(
    crs_n: CRSn,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening,
    K: Sequence[int],
) -> Opening:
    """``VC.Disagg`` —— 把大集合的证明拆成小集合的证明。对应清单 **#23**。

    要求 ``K ⊆ I``。论文原文::

        S_K ← S_I^{e_{I\\K}}
        χ_j = S_K^{1/e_j} ← S_I^{e_{I\\(K∪{j})}}      对每个 j ∈ I\\K
        Λ_K ← Λ_I^{e_{I\\K}} · ∏_{j∈I\\K} χ_j^{v_j}

    把 :math:`χ_j` 的指数展开可以看清它在干什么：

    .. math::
        \\chi_j = S_I^{\\,e_{I\\setminus K}/e_j} = g^{\\,e_{[n]}/(e_K e_j)}

    所以 :math:`\\prod_{j \\in I \\setminus K} \\chi_j^{v_j}
    = \\prod_{j \\in I \\setminus K} \\left(g^{\\,e_{[n]}/(e_K e_j)}\\right)^{v_j}` ——
    正是 :math:`\\Lambda_K` 定义里「``j ∉ K`` 且在 ``I`` 内」那一部分，
    于是加上 :math:`\\Lambda_I^{e_{I\\setminus K}}`（来自 ``j ∉ I`` 那部分）
    就凑齐了完整的 :math:`\\Lambda_K`。

    实现上这一步走 :func:`~svc.mathbase.weighted_root_product`，
    底数取 :math:`S_I`、指数集合取 :math:`\\{e_j : j \\in I \\setminus K\\}` ——
    因为它的 :math:`X = e_{I\\setminus K}`，正好给出
    :math:`S_I^{e_{I\\setminus K}/e_j}`。
    """
    I_set = as_index_set(I)
    K_set = as_index_set(K)
    if not set(K_set) <= set(I_set):
        raise ValueError("disagg 要求 K ⊆ I")
    if pi_I.I and pi_I.I != I_set:
        raise ValueError("传入的 I 与证明里的下标集合不一致")

    val_of = dict(zip(I_set, vals_I))
    primegen = crs_n.crs.primegen
    N = crs_n.N
    K_set_of = set(K_set)

    # ---- 顺序把 I \ K 里的每个位置「加回」摘要 ----
    #
    # 视角：pi_I = d(v \ I)，目标是 d(v \ K)。而 I \ K 正是要「加回来」的那些位置，
    # 于是逐个 :func:`add_back` 即可。
    #
    # 与论文公式的等价性（E = I \ K）：
    #   S_K   = S_I^{e_E}                 —— add_back 里 S 逐步乘 e_j 自然得到
    #   Λ_K   = Λ_I^{e_E} · ∏_{j∈E} χ_j^{v_j}， χ_j = S_I^{e_E/e_j}
    # 差一个位置就多乘一个因子，展开后与逐步结果逐项对应（已由测试与直算对拍）。
    #
    # 代价从 O(ℓ|E| log|E|)（需要一次 root_factor）降到 O(ℓ|E|)。
    S, Lam = pi_I.S_I, pi_I.Lambda_I
    for j in I_set:
        if j in K_set_of:
            continue
        S, Lam = add_back(S, Lam, primegen.get(j), val_of[j], N)

    return Opening(S_I=S, Lambda_I=Lam, I=K_set)


def agg(
    crs_n: CRSn,
    I: Sequence[int],
    vals_I: Sequence[int],
    pi_I: Opening,
    J: Sequence[int],
    vals_J: Sequence[int],
    pi_J: Opening,
) -> Opening:
    """``VC.Agg`` —— 合并两个证明。对应清单 **#24**。

    「前提：两个集合不相交，否则先用 :func:`disagg` 消掉重叠部分。」
    （论文原文：「if this is not the case, one could simply disaggregate
    ``π_I`` (or ``π_J``) to ``π_{I\\\\J}`` (or ``π_{J\\\\I}``)」）

    论文原文五步::

        S_K ← ShamirTrick(S_I, S_J, e_I, e_J)
        φ_j ← S_K^{e_{J\\{j}}}   (j ∈ J)      ψ_i ← S_K^{e_{I\\{i}}}   (i ∈ I)
        ρ_I ← Λ_I / ∏_{j∈J} φ_j^{v_j}
        σ_J ← Λ_J / ∏_{i∈I} ψ_i^{v_i}
        Λ_K ← ShamirTrick(ρ_I, σ_J, e_I, e_J)

    第四步「除交叉项」为什么必须（清单原文已经说透了）：:: 

        Λ_I 里属于 J 的那部分是 1/e_I 次方，
        而 Λ_K 里应该是 1/(e_I·e_J) 次方，次数不匹配，直接相乘会重复计数。

    用群除法（:func:`~svc.mathbase.group_div`）而不是指数相减，
    是因为「群元素可以相除，指数不能相减」—— 我们不知道群的阶，
    指数上的运算必须在整数层面完成，而 :math:`\\prod φ_j^{v_j}` 本身就是
    一个可以算出来的群元素，直接除即可。

    :math:`\\prod_{j \\in J} \\varphi_j^{v_j}` 用
    :func:`~svc.mathbase.weighted_root_product` 一次算完
    （:math:`\\varphi_j = S_K^{e_J/e_j}`，与 ``X = e_J`` 的形式吻合）。

    这个算法是**增量可聚合**的核心：合并结果 :math:`\\pi_K` 仍然是一个合法的
    子向量打开证明，可以再次参与合并，因此**合并次数不限、合并顺序任意**。
    """
    I_set = as_index_set(I)
    J_set = as_index_set(J)

    if set(I_set) & set(J_set):
        raise ValueError(
            "agg 要求 I ∩ J = ∅；有重叠时请先用 disagg 把重叠部分去掉"
        )
    if pi_I.I and pi_I.I != I_set:
        raise ValueError("pi_I 里的下标集合与传入的 I 不一致")
    if pi_J.I and pi_J.I != J_set:
        raise ValueError("pi_J 里的下标集合与传入的 J 不一致")

    primegen = crs_n.crs.primegen
    e_I = e_of(primegen, I_set)
    e_J = e_of(primegen, J_set)

    # 第一步：Shamir 技巧合并 S。要求 gcd(e_I, e_J) = 1 —— 集合不相交保证了这点。
    # 注意：两个 Opening 的字段名都是 S_I（各自代表自己集合的 S），
    # 这里 pi_J.S_I 就是论文里的 S_J。
    S_K = shamir_trick(pi_I.S_I, pi_J.S_I, e_I, e_J, crs_n.N)
    if S_K is None:
        raise ValueError(
            "ShamirTrick 失败：两个根不同源，或 gcd(e_I, e_J) ≠ 1。"
            "最常见的原因是素数映射发生了碰撞（哈希版在位数太小时会撞）"
        )

    val_I = dict(zip(I_set, vals_I))
    val_J = dict(zip(J_set, vals_J))

    # 第四步的交叉项
    if J_set:
        prod_phi = weighted_root_product(
            S_K,
            [val_J[j] for j in J_set],
            [primegen.get(j) for j in J_set],
            crs_n.N,
        )
    else:
        prod_phi = 1

    if I_set:
        prod_psi = weighted_root_product(
            S_K,
            [val_I[i] for i in I_set],
            [primegen.get(i) for i in I_set],
            crs_n.N,
        )
    else:
        prod_psi = 1

    rho_I = group_div(pi_I.Lambda_I, prod_phi, crs_n.N)
    sigma_J = group_div(pi_J.Lambda_I, prod_psi, crs_n.N)

    # 第五步
    Lambda_K = shamir_trick(rho_I, sigma_J, e_I, e_J, crs_n.N)
    if Lambda_K is None:
        raise ValueError("ShamirTrick 合并 Λ 失败（与上面同因）")

    K_set = as_index_set(list(I_set) + list(J_set))
    return Opening(S_I=S_K, Lambda_I=Lambda_K, I=K_set)


# ===========================================================================
# 五、可选加速（清单 #25 ~ #26）
# ===========================================================================

def disagg_one_to_many(
    crs_n: CRSn,
    B: int,
    all_indices: Sequence[int],
    vals: Sequence[int],
    pi: Opening,
) -> list[tuple[tuple[int, ...], tuple[int, ...], Opening]]:
    """把整体证明一次拆成 ``n/B`` 个块的证明。对应清单 **#25**。

    :param B: 每块的元素个数
    :param all_indices: 整体证明覆盖的下标（通常是全部 ``[n]``）
    :param vals: 整个向量的值
    :param pi: 整体证明 :math:`\\pi_I`
    :returns: ``[(块下标, 块的值, 块证明), ...]``

    实现上做了两件事：

    1. **``S`` 部分一次全算**：对全体素数做一次
       :func:`~svc.mathbase.batch_root_factor_general`
       （``chunk = B``），第 ``b`` 块直接得到
       :math:`S_I^{e_I/e_{K_b}} = S_{K_b}`。
       若按 :func:`disagg` 逐块算，每块一次大指数模幂，``n = 2^{16}`` 时
       单块就要一两分钟，完全不可用。
    2. **``Λ`` 部分逐块用** :func:`~svc.mathbase.weighted_root_product`，
       把每块的代价压到一次分治 + ``|I\\K_b|`` 次小指数模幂。

    .. warning::

       **复杂度还是要说清楚**：第 2 步对每个块都要在 ``n - B`` 个元素上做一次
       分治，共 ``n/B`` 个块，总代价约
       :math:`O\\big(\\tfrac{n^2}{B} \\log(n-B)\\big)` 次模乘。
       ``n = 2^{16}``、``B = 1024`` 时这个量级在 CPython 下仍然偏大，
       实用规模大致到 ``n ≈ 2^{12}``。

       **要跑大规模请用** :func:`agg_many_to_one` **那条路**：
       它只在被检索到的那几个块上做 :func:`agg`，代价与**检索的块数**成正比，
       而不是与 ``n²/B`` 成正比 —— 这正是论文强调「增量聚合」的意义所在。
    """
    if B <= 0:
        raise ValueError("B 必须为正")

    I_set = as_index_set(all_indices)
    if pi.I and pi.I != I_set:
        raise ValueError("传入的下标集合与证明里的不一致")
    if not I_set:
        return []

    out: list[tuple[tuple[int, ...], tuple[int, ...], Opening]] = []
    _split_digest(
        pi.S_I,
        pi.Lambda_I,
        list(I_set),
        list(vals),
        max(1, int(B)),
        crs_n.crs.primegen,
        crs_n.N,
        out,
    )
    return out


def _split_digest(
    S: int,
    Lam: int,
    idx: list[int],
    vals: list[int],
    B: int,
    primegen: PrimeGen | PrimeGenHash,
    N: int,
    out: list,
) -> None:
    """递归二分：把 :math:`d(\\mathbf{v} \\setminus I)` 拆成各块的摘要。

    设当前摘要对应下标集合 ``I``（即手里是 :math:`d(\\mathbf{v} \\setminus I)`）。
    把 ``I`` 分成左右两半 ``L``、``R``，则：

    * :math:`d(\\mathbf{v} \\setminus L)` = 把 ``R`` 加回去
    * :math:`d(\\mathbf{v} \\setminus R)` = 把 ``L`` 加回去

    两边都是 :func:`add_back` 的循环，各需要 ``|R|`` 与 ``|L|`` 次，
    合计正好 ``|I|`` 次。于是递归代价满足
    :math:`T(m) = 2T(m/2) + m`，即 :math:`O(m \\log(m/B))` ——
    比「对每块单独从原证明拆一次」（:math:`O(m^2/B)`）快一个数量级。

    这正是 Campanelli 等人描述的「先取根（整向量证明），再递归拆成两半」的做法；
    他们在论文里报的是 :math:`O(\\ell n \\log^2 n)`，
    而用上面这个更快的拆分法实际是 :math:`O(\\ell n \\log n)`。
    """
    if len(idx) <= B:
        out.append(
            (
                tuple(idx),
                tuple(vals[i] for i in idx),
                Opening(S, Lam, tuple(idx)),
            )
        )
        return

    half = len(idx) // 2
    left, right = idx[:half], idx[half:]

    # 左半：把右半加回去
    S_l, Lam_l = S, Lam
    for j in right:
        S_l, Lam_l = add_back(S_l, Lam_l, primegen.get(j), vals[j], N)

    # 右半：把左半加回去
    S_r, Lam_r = S, Lam
    for j in left:
        S_r, Lam_r = add_back(S_r, Lam_r, primegen.get(j), vals[j], N)

    _split_digest(S_l, Lam_l, left, vals, B, primegen, N, out)
    _split_digest(S_r, Lam_r, right, vals, B, primegen, N, out)


def agg_many_to_one(
    crs_n: CRSn,
    proofs: Sequence[tuple[Sequence[int], Sequence[int], Opening]],
) -> Opening:
    """分治合并多个块的证明，得到一个总证明。对应清单 **#26**。

    :param proofs: ``[(下标集合, 该集合的值, 该集合的证明), ...]``，**两两不相交**
    :returns: 覆盖全部下标并集的单个证明

    这是 VDS 检索流程的主力：多个存储节点各返回自己那块的
    ``(F_Q, π_Q)``，客户端把它们合成**一个**证明，验证代价与块数无关。

    分治策略：每一轮把相邻两两合并，轮数 ``log k``（``k`` 为块数）。
    每轮内部各对之间不相交，所以 :func:`agg` 的前提始终满足。
    合并顺序任意 —— 这正是论文「增量可聚合」性质要保证的：
    :func:`agg` 的输出仍是合法打开证明，可以继续参与合并。
    """
    items = [
        (as_index_set(ids), tuple(vals), pi) for ids, vals, pi in proofs
    ]
    if not items:
        raise ValueError("proofs 不能为空")
    if len(items) == 1:
        return items[0][2]

    while len(items) > 1:
        nxt = []
        for i in range(0, len(items) - 1, 2):
            ids_a, vals_a, pi_a = items[i]
            ids_b, vals_b, pi_b = items[i + 1]
            merged = agg(
                crs_n, ids_a, vals_a, pi_a, ids_b, vals_b, pi_b
            )
            # 值必须按 merged.I 的顺序重排：agg 返回的是升序并集，
            # 不等于 vals_a + vals_b 的拼接顺序。顺序错了下一轮 agg
            # 会把值安到错的下标上，而且不会报错、只会默默算错。
            valmap = dict(zip(ids_a, vals_a))
            valmap.update(dict(zip(ids_b, vals_b)))
            nxt.append(
                (
                    merged.I,
                    tuple(valmap[i] for i in merged.I),
                    merged,
                )
            )
        if len(items) & 1:
            nxt.append(items[-1])  # 落单的直接带到下一轮
        items = nxt

    return items[0][2]


# ---------------------------------------------------------------------------
# 别名：清单 #21 里这个函数就叫 ``open``，与 Python 内置函数重名。
# 主名用 open_subvector，这里在**模块级**再挂一个别名，
# 这样 ``svc.scheme.open(...)`` 按清单的名字可用，
# 同时 ``from svc.scheme import *`` 不会把内置 open 遮掉（__all__ 里没它）。
# ---------------------------------------------------------------------------
open = open_subvector
