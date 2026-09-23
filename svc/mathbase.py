"""数学底座 —— 对应 to-do-function-list.txt 第一部分（函数 1~8）。

本模块是**纯数学工具层**，不含任何方案逻辑，因此可以脱离 SVC 单独测试。
所有涉及取模的运算都以 ``n``（隐藏阶群的模数）为模。

====================  ==================================================
清单编号               函数
====================  ==================================================
1                    :func:`is_probable_prime`
2                    :func:`hash_prime`
3                    :func:`egcd`
4                    :func:`mod_inverse`
5                    :func:`group_div`
6                    :func:`shamir_trick`
7                    :func:`multiexp`
8                    :func:`batch_root_factor` / :func:`batch_root_factor_general`
====================  ==================================================

设计说明
--------
* 全程只用 Python 整数（任意精度），**不依赖任何第三方库**。
* ``pow(a, e, n)`` 是 Python 内置的三参数模幂，底层是 CPython 的
  ``long_pow``，性能与 GMP 同量级，不需要自己写快速幂。
* 互素性是**方案正确性的硬前提**：如果两个素指数相等，``shamir_trick``
  会失败。因此本模块对不满足前提的情况一律**显式返回 ``None`` 或抛异常**，
  绝不静默返回错误结果。
"""

from __future__ import annotations

import hashlib
from functools import reduce
from math import gcd, isqrt
from operator import mul
from typing import Iterable, Sequence

__all__ = [
    "is_probable_prime",
    "is_bpsw_prime",
    "next_prime",
    "hash_prime",
    "egcd",
    "mod_inverse",
    "group_div",
    "shamir_trick",
    "multiexp",
    "weighted_root_product",
    "batch_root_factor",
    "batch_root_factor_general",
    "batch_root_factor_any",
    "product_tree",
    "prod",
]


# ---------------------------------------------------------------------------
# 小工具
# ---------------------------------------------------------------------------

def prod(xs: Iterable[int]) -> int:
    """连乘。空序列返回 1（乘法的单位元）。"""
    return reduce(mul, xs, 1)


def product_tree(xs: Sequence[int]) -> int:
    """平衡二叉树连乘。

    为什么不能用 ``prod``（左到右连乘）
    ----------------------------------
    ``e_{[n]} = ∏ e_i`` 里每个 ``e_i`` 有 ``l+1`` 位，结果有 ``n(l+1)`` 位。
    左到右连乘时，第 ``k`` 步要把一个已经很大的数乘以 ``e_k``，
    总代价是 :math:`O(n^2 L)`（``L = l+1``）。
    平衡树让每一层的总位长恒定，代价降到 :math:`O(n L \\log n)`。

    ``n = 2^{16}``、``L = 129`` 时两者相差两个数量级（秒 vs 小时）。
    """
    items = list(xs)
    if not items:
        return 1
    while len(items) > 1:
        nxt: list[int] = []
        # 两两相乘，落单的直接带到下一层
        for i in range(0, len(items) - 1, 2):
            nxt.append(items[i] * items[i + 1])
        if len(items) & 1:
            nxt.append(items[-1])
        items = nxt
    return items[0]


#: 试除用的小素数表。先用它筛掉绝大多数合数，比直接上 Miller-Rabin 快得多。
_SMALL_PRIMES: tuple[int, ...] = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
)


# ---------------------------------------------------------------------------
# 1. is_probable_prime
# ---------------------------------------------------------------------------

def jacobi_symbol(a: int, n: int) -> int:
    r"""Jacobi 符号 :math:`\left(\frac{a}{n}\right)`，``n`` 必须是正奇数。

    只用二次互反律迭代，不做因式分解（:math:`O(\log^2 n)` 次位运算）。
    Lucas 判据要靠它挑参数 ``D``。
    """
    if n <= 0 or n % 2 == 0:
        raise ValueError("Jacobi 符号要求 n 是正奇数")
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def _lucas_uv(n: int, P: int, Q: int, D: int, k: int) -> tuple[int, int, int]:
    r"""Lucas 数列的第 ``k`` 项 ``(U_k, V_k, Q^k) mod n``。

    用二进制链（只有乘法和平方，不出现除法）：

    .. math::

        U_{2m} = U_m V_m, \qquad V_{2m} = V_m^2 - 2Q^m \\
        U_{2m+1} = \frac{P U_{2m} + V_{2m}}{2}, \qquad
        V_{2m+1} = \frac{D U_{2m} + P V_{2m}}{2}

    除以 2 在模 ``n``（奇数）下就是乘 ``(n+1)/2``。
    """
    if k == 0:
        return 0, 2, 1
    inv2 = (n + 1) // 2
    Qmod = Q % n
    U, V, Qk = 1, P % n, Qmod
    for bit in bin(k)[3:]:          # 从次高位开始
        U, V = U * V % n, (V * V - 2 * Qk) % n
        Qk = Qk * Qk % n
        if bit == "1":
            U, V = (P * U + V) * inv2 % n, (D * U + P * V) * inv2 % n
            Qk = Qk * Qmod % n
    return U, V, Qk


def is_strong_lucas_prp(n: int) -> bool:
    r"""强 Lucas 可能素数判据（Selfridge 参数法）。

    参数选取：取 :math:`D = 5, -7, 9, -11, \dots` 中第一个满足
    :math:`\left(\frac{D}{n}\right) = -1` 的，然后
    :math:`P = 1,\ Q = (1 - D)/4`。写 :math:`n + 1 = d \cdot 2^s`（``d`` 为奇数），
    若

    .. math::

        U_d \equiv 0 \pmod n \quad \text{或} \quad
        \exists\, 0 \le r < s:\ V_{d \cdot 2^r} \equiv 0 \pmod n

    则通过。

    单独用它是**有已知反例**的（不像 BPSW 那样至今无反例），
    所以真正的判据是 :func:`is_bpsw_prime`。
    """
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    # 完全平方数直接排除：它的 Jacobi(D, n) 永远不会是 -1，搜索不会终止
    r = isqrt(n)
    if r * r == n:
        return False

    D = 5
    while True:
        j = jacobi_symbol(D, n)
        if j == -1:
            break
        if j == 0:
            g = gcd(abs(D), n)
            if g < n:
                return False            # 撞出一个非平凡因子，直接合数
            # n | |D|：n 自己就是那个小因子，与 D 撞上了，换下一个
        D = -(D + 2) if D > 0 else 2 - D

    P, Q = 1, (1 - D) // 4

    # n + 1 = d * 2^s
    d = n + 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1

    U, V, Qk = _lucas_uv(n, P, Q, D, d)
    if U == 0 or V == 0:
        return True
    for _ in range(s - 1):
        V = (V * V - 2 * Qk) % n
        Qk = Qk * Qk % n
        if V == 0:
            return True
    return False


def is_bpsw_prime(n: int) -> bool:
    r"""Baillie-PSW 判据：**base-2 强可能素数** 且 **强 Lucas 可能素数**。

    为什么用它
    ----------
    Miller-Rabin 的「误判概率 :math:`\le 4^{-k}`」只在基是**真随机**时成立。
    本实现原先的基由 ``sha256(n)`` 派生 —— 也就是基序列是 ``n`` 的**确定性函数**，
    那条概率界并不适用（要保「同一个 n 结论可复现」，就不能取真随机基）。

    所以这里改用 BPSW：它**完全是 ``n`` 的确定性函数**（可复现），
    同时至今**没有一个已知反例** —— 包括把所有 base-2 强伪素数逐个排除。
    已知最小的「过 base-2 但被 Lucas 拦下」的合数是 2047。

    与 BPSW 的通行定义一致：先试除小素数、再查完全平方，
    然后 base-2 强可能素数 + 强 Lucas 两条都过才算。

    :returns: ``True`` 表示（在该判据下）是素数
    """
    if n < 2:
        return False
    if n < 4:
        return True                       # 2, 3
    if n % 2 == 0:
        return False

    for p in _SMALL_PRIMES:
        if n == p:
            return True
        if n % p == 0:
            return False

    r = isqrt(n)
    if r * r == n:
        return False                      # 完全平方数一定是合数

    # 第一条：base-2 强可能素数
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(2, d, n)
    if x != 1 and x != n - 1:
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False

    # 第二条：强 Lucas
    return is_strong_lucas_prp(n)


def is_probable_prime(
    n: int, rounds: int | None = None, *, bpsw: bool = True
) -> bool:
    r"""素性判定。对应清单 **#1**。

    :param n: 待判定整数
    :param rounds: **额外**再跑多少轮 Miller-Rabin 基。``None``（默认）表示不额外跑。
    :param bpsw: 超出确定性基的覆盖范围后，是否用 :func:`is_bpsw_prime`
                 作判据（默认 ``True``）。

    行为
    ----
    * ``n < 2`` → ``False``；小素数试除可判定的直接给出结论（筛掉 ~88% 的合数）
    * 对 ``n < 3.3e24``，用确定性的固定基集合，结论**一定正确**
      （这一条是 Laarhoven 的界：前 12 个素数作基就足够）
    * 对更大的 ``n``，用 :func:`is_bpsw_prime`（base-2 强可能素数 + 强 Lucas）

    关于随机性
    ----------
    本函数原先在超界之后用 ``sha256(n)`` 派生的 LCG 生成「随机基」。
    那是**确定性序列**，不是随机基 —— MR 那条 :math:`\\le 4^{-k}` 的界
    对它并不成立（审计【6】）。现在改走 BPSW：它同样只依赖 ``n``，
    所以「同一个 ``n`` 结论可复现」（这是原设计要保的性质）没丢，
    但它至今**没有已知反例**，比任何固定轮数的确定性 MR 基都强。

    :param rounds: 若显式给出正数，就在 BPSW 之外**再**跑 ``rounds`` 轮
                   MR 基（基仍由 ``n`` 派生）—— 作为多一道保险，
                  不再声称它带来 :math:`4^{-k}` 的界。
    """
    if n < 2:
        return False
    if n < 4:
        return True  # 2, 3

    for p in _SMALL_PRIMES:
        if n == p:
            return True
        if n % p == 0:
            return False

    # n - 1 = d * 2^s，其中 d 为奇数
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1

    def _is_witness_to_compositeness(a: int) -> bool:
        """返回 True 表示 a 证明了 n 是合数。"""
        a %= n
        if a == 0:
            return False
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            return False
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                return False
        return True

    # 第一组：确定性基。对 n < 3.3e24 这组基给出的是**可证明正确**的结论。
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a >= n:
            break
        if _is_witness_to_compositeness(a):
            return False

    if n < 3_317_044_064_679_887_385_961_981:
        # 上面的基已覆盖该范围，结论确定
        return True

    # 第二组：超出确定基的覆盖范围 —— 用 BPSW
    if bpsw and not is_bpsw_prime(n):
        return False

    # 第三组（可选）：显式要求的额外 MR 轮数。
    # 基由 n 派生（可复现），但它是确定性序列，所以这里不声称 4^-rounds 的界。
    if rounds:
        seed = hashlib.sha256(n.to_bytes((n.bit_length() + 7) // 8, "big")).digest()
        state = int.from_bytes(seed, "big")
        for _ in range(rounds):
            state = (state * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            a = 2 + state % (n - 3)
            if _is_witness_to_compositeness(a):
                return False
    return True


def next_prime(n: int) -> int:
    """返回 ``>= n`` 的最小素数。供双射版素数映射 :class:`~svc.primegen.PrimeGen` 使用。

    ``n <= 2`` 时返回 2。偶数会先被抬到下一个奇数，避免浪费一次试除。
    """
    if n <= 2:
        return 2
    if n % 2 == 0:
        n += 1
    while not is_probable_prime(n):
        n += 2
    return n


# ---------------------------------------------------------------------------
# 2. hash_prime
# ---------------------------------------------------------------------------

def hash_prime(data: bytes, out_bytes: int = 16, max_tries: int = 1 << 20) -> int:
    """把字节串哈希成素数：反复哈希直到结果是素数。对应清单 **#2**。

    :param data: 输入字节串
    :param out_bytes: 输出素数的字节长度。默认 16 → 128 位素数（与论文一致）。
    :param max_tries: 上限保护，防止 ``out_bytes`` 过小导致死循环。

    :raises RuntimeError: 超过 ``max_tries`` 仍未找到素数。

    .. warning::

       **本函数只在选用「哈希版」素数映射（清单 #11）时才需要**，
       方案本体（含清单 #10 的双射版）完全用不到它。

       哈希版的固有缺陷：它会**碰撞**。位长越小越容易撞；一旦两个下标映射到
       同一个素数，后面所有「互素性」假设全部崩塌，``shamir_trick`` 会静默
       给出错误结果。所以正式使用请走 :class:`~svc.primegen.PrimeGen`（双射，
       天然无碰撞）。

    实现细节：第 k 次尝试把 ``k`` 以 8 字节大端前缀拼在 ``data`` 前面再哈希，
    因此同一个 ``data`` 的输出是确定的（可复现），而不是随机的。
    """
    if out_bytes < 1:
        raise ValueError("out_bytes 必须 >= 1")

    for counter in range(max_tries):
        h = hashlib.blake2b(digest_size=out_bytes + 8)
        h.update(counter.to_bytes(8, "big"))
        h.update(data)
        candidate = int.from_bytes(h.digest()[:out_bytes], "big")
        # 强制置最高位，保证位长稳定（否则前导零会让素数位数偏小）
        candidate |= 1 << (out_bytes * 8 - 1)
        if is_probable_prime(candidate):
            return candidate

    raise RuntimeError(
        f"hash_prime: {max_tries} 次尝试仍未找到素数（out_bytes={out_bytes}）"
    )


# ---------------------------------------------------------------------------
# 3~5. egcd / mod_inverse / group_div
# ---------------------------------------------------------------------------

def egcd(a: int, b: int) -> tuple[int, int, int]:
    """扩展欧几里得。对应清单 **#3**。

    返回 ``(g, x, y)`` 满足 ``a*x + b*y = g = gcd(a, b)``。
    ``a``、``b`` 可以是负数，结果仍然成立。
    """
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    # 归一化：gcd 按惯例取非负。否则 a、b 一负一正时返回值可能为负，
    # 调用方写 `if g != 1` 会被 -1 骗过去。
    # 恒等式 a*x + b*y = g 在同时取反后仍然成立。
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def mod_inverse(a: int, n: int) -> int:
    """求 ``a`` 关于 ``n`` 的模逆元。对应清单 **#4**。

    只用 ``n``，**不需要群阶**（这正是隐藏阶群方案能成立的关键：
    我们不知道 ord(g)，但求模逆只依赖 N）。

    :raises ValueError: ``gcd(a, n) != 1`` 时无逆元。
    """
    if n <= 0:
        raise ValueError("模数必须为正")
    a %= n
    if a == 0:
        raise ValueError("0 没有模逆元")
    g, x, _ = egcd(a, n)
    if g != 1:
        raise ValueError(f"{a} 关于 {n} 没有模逆元（gcd = {g}）")
    return x % n


def group_div(a: int, b: int, n: int) -> int:
    """群除法：``a * b^(-1) mod n``。对应清单 **#5**。

    聚合算法第四步「除交叉项」用它 —— 只有群元素之间能相除，
    指数（素数乘积）之间不能，这是本方案能正确消掉重复计数的原因。

    :raises ValueError: ``b`` 不可逆时。
    """
    return (a % n) * mod_inverse(b, n) % n


# ---------------------------------------------------------------------------
# 6. shamir_trick
# ---------------------------------------------------------------------------

def shamir_trick(root_x: int, root_y: int, x: int, y: int, n: int) -> int | None:
    """Shamir 技巧：由 ``g^(1/x)`` 与 ``g^(1/y)`` 算出 ``g^(1/(xy))``。对应清单 **#6**。

    做法：用 :func:`egcd` 求 ``a*x + b*y = 1``，返回
    ``root_x^b * root_y^a mod n``。

    为什么对：设两个根同源于某个 ``g``，则

    .. math::
        (root_x^b \\cdot root_y^a)^{xy} = (root_x^x)^{by} \\cdot (root_y^y)^{ax}
        = g^{by} \\cdot g^{ax} = g^{ax+by} = g

    所以 ``root_x^b * root_y^a`` 确实是 ``g`` 的 ``1/(xy)`` 次方根。

    两道**必须的**自检（清单明确要求）：

    1. **同源自检**：``root_x^x == root_y^y (mod n)``？否则两个根不是同一个
       ``g`` 的根，合并出来的东西没有意义 → 返回 ``None``。
       注意这**不是**在验证证明，只是防止调用方把不相关的两个根塞进来。
    2. **互素自检**：``gcd(x, y) == 1``？否则 Bézout 系数 ``a, b`` 求出来
       满足的是 ``ax + by = d > 1``，直接代进去会**静默返回错误结果**
       （不是崩溃，是算错，最难查）→ 返回 ``None``。

    :returns: 合并后的根，或 ``None`` 表示前提不满足。
    """
    if pow(root_x, x, n) != pow(root_y, y, n):
        return None

    d, a, b = egcd(x, y)
    if d != 1:
        return None

    # a、b 可能为负：负指数走模逆。x、y 都是奇素数，Bézout 系数必然一正一负。
    lhs = _pow_signed(root_x, b, n)
    rhs = _pow_signed(root_y, a, n)
    if lhs is None or rhs is None:
        return None
    return lhs * rhs % n


def _pow_signed(a: int, e: int, n: int) -> int | None:
    """支持负指数的模幂。负指数先求模逆，求不出返回 ``None``。"""
    if e == 0:
        return 1
    if e > 0:
        return pow(a, e, n)
    try:
        a_inv = pow(a, -1, n)
    except ValueError:
        return None
    return pow(a_inv, -e, n)


# ---------------------------------------------------------------------------
# 7. multiexp
# ---------------------------------------------------------------------------

def multiexp(alphas: Sequence[int], xs: Sequence[int], n: int) -> int:
    """分治计算 ``∏_i alphas[i] ** (x / xs[i]) mod n``，其中 ``x = ∏_i xs[i]``。对应清单 **#7**。

    :param alphas: 一组群元素
    :param xs: 一组正整数，长度必须与 ``alphas`` 相同
    :param n: 模数
    :returns: 单个群元素

    **用途**（清单原文）：「把 ``1/e_I`` 次方摊成每一项一个整数指数，
    从而不用真的求根」。

    具体到方案里，``Λ_I`` 本来是 ``(∏_{j∉I} S_j^{y_j}) ** (1/e_I)``。
    群元素整体的 ``e_I`` 次根**求不出来**（那正是 RSA 假设），
    但把 ``1/e_I`` 摊开后每一项的指数是整数 ``e_[n]/(e_j·e_I)``，
    于是每项都是一个普通模幂。本函数就是把这件事机械化的工具。

    正确性（分治）
    --------------
    设 ``m = len(xs)``、``h = m // 2``、``x_L = ∏ xs[:h]``、``x_R = ∏ xs[h:]``，
    则 ``x = x_L · x_R``，对左半边的 ``i`` 有::

        alphas[i] ** (x / xs[i]) = (alphas[i] ** x_R) ** (x_L / xs[i])

    所以把左半边每个底数先抬 ``x_R`` 次方、右半边每个底数先抬 ``x_L`` 次方，
    再递归，最后把两半的乘积相乘即可。基例 ``m == 1`` 时 ``x / xs[0] == 1``，
    直接返回 ``alphas[0]``。

    .. note::

       **复杂度说明**：这个分治把工作量减半层——
       ``m·(x_R)`` 的总位长逐层折半，总代价 ``O(m²·L)``（``L`` 是单个 ``x_i`` 的位长），
       比朴素做法的 ``O(m²·L)`` 常数小约 2 倍，**不是真正意义的 O(m log k)**。

       清单里说的 ``O(k log k)`` 指的是**同底数**情形：此时所有
       ``alphas[i] = g^{y_i}``，只要用 :func:`batch_root_factor` 一次性算出
       ``{g^{x/xs[i]}}``（那是货真价实的 ``O(k log k)``），再对各次幂加权相乘即可。
       该高效路径由 :func:`weighted_root_product` 提供，``lambda_subset`` 走的就是它。
    """
    if len(alphas) != len(xs):
        raise ValueError("alphas 与 xs 长度必须一致")
    if len(alphas) == 0:
        return 1
    return _multiexp_rec(list(alphas), list(xs), n)


def _multiexp_rec(alphas: list[int], xs: list[int], n: int) -> int:
    m = len(xs)
    if m == 1:
        # x / xs[0] == 1
        return alphas[0] % n

    h = m // 2
    x_left = prod(xs[:h])
    x_right = prod(xs[h:])

    # 左半边的底数抬 x_right 次方，右半边抬 x_left 次方
    left_alphas = [pow(a, x_right, n) for a in alphas[:h]]
    right_alphas = [pow(a, x_left, n) for a in alphas[h:]]

    return (
        _multiexp_rec(left_alphas, xs[:h], n)
        * _multiexp_rec(right_alphas, xs[h:], n)
    ) % n


def weighted_root_product(
    g: int,
    ys: Sequence[int],
    xs: Sequence[int],
    n: int,
) -> int:
    """高效版 multiexp：``∏_i (g^{ys[i]}) ** (x / xs[i]) mod n``，``x = ∏ xs``。

    这就是 :func:`multiexp` 文档里说的「同底数」情形，也是 ``Λ_I`` 的实际算法
    （清单 #15 的 PS：「先算 ``S_j`` 的 ``1/e_I`` 次方，再乘方 ``v_i``」）。

    做法只有两步：

    1. ``ts = batch_root_factor(g, xs, n)`` → ``ts[i] = g^(x/xs[i])``（分治，便宜）
    2. ``∏ ts[i] ** ys[i] mod n`` → 每个 ``ys[i]`` 只有 ``l`` 位，是很便宜的模幂

    对比朴素做法（对每个 ``i`` 直接算 ``pow(g, x // xs[i], n)``）：
    朴素做法里每个指数都有 ``(k-1)·L`` 位，总共 ``k`` 次这种巨大模幂；
    这里第一步只有分治的 ``O(k log k)`` 代价，第二步全是 ``l`` 位的小指数。
    """
    if len(ys) != len(xs):
        raise ValueError("ys 与 xs 长度必须一致")
    if len(xs) == 0:
        return 1
    if len(xs) == 1:
        # x / xs[0] == 1，整体退化成 (g^{ys[0]})^1
        return pow(g, ys[0], n)

    # 用任意长度版本：方案里的下标个数（例如 |I \ K|）不一定是 2 的幂
    ts = batch_root_factor_any(g, list(xs), n)
    acc = 1
    for t, y in zip(ts, ys):
        if y:
            acc = acc * pow(t, y, n) % n
    return acc


# ---------------------------------------------------------------------------
# 8. batch_root_factor
# ---------------------------------------------------------------------------

def batch_root_factor(g: int, xs: Sequence[int], n: int) -> list[int]:
    """一次算出全部的「除自己那个之外全部 ``xs`` 之积」次方。对应清单 **#8**。

    输入 ``g`` 与 ``xs = [x_1, ..., x_m]``，记 ``X = ∏ xs``，
    返回长度为 ``m`` 的列表，第 ``i`` 项是::

        g ** (X / x_i)  mod n

    **这是承诺阶段一次性产出所有** ``S_i`` **的引擎**：

    .. math::
        S_i = g^{e_{[n]} \\setminus \\{i\\}} = g^{e_{[n]} / e_i}

    对 ``e_i`` **整除** ``e_{[n]}``，所以指数是整数除法，直接模幂 ——
    **不需要开方**，这正是 CF13 方案能公开计算的原因。

    :param xs: 长度必须是 2 的幂（分治要求）。

    .. note::

       清单原文：「前期使用 13（:func:`~svc.scheme.s_iota` 逐项算）进行 debug，
       这里的 8 算大量内容更快，但是出错不好修」。
       所以 :func:`~svc.scheme.commit` 提供了 ``use_batch`` 开关，
       小规模用逐项、大规模用本函数，两条路径互相验证。
    """
    if len(xs) == 0:
        return []
    _check_power_of_two(len(xs))
    return batch_root_factor_general(g, list(xs), 1, n)


def batch_root_factor_general(
    g: int,
    xs: Sequence[int],
    chunk: int,
    n: int,
) -> list[int]:
    """支持分块粒度的批量求根（对应 Rust ``root_factor_general``）。

    返回值长度为 ``len(xs) / chunk``，第 ``j`` 项是
    ``g ** (X / X_j) mod n``，其中 ``X_j`` 是第 ``j`` 块内 ``xs`` 的乘积。

    ``chunk = 1`` 时退化为 :func:`batch_root_factor`。
    预计算模式下（清单 #25/#26）会用到 ``chunk > 1`` 来减少元素个数。

    :param chunk: 每块的元素个数，必须是 2 的幂。
    """
    if len(xs) == 0:
        return []
    _check_power_of_two(len(xs))
    _check_power_of_two(chunk)
    return _root_factor_rec(g, list(xs), chunk, n)


def batch_root_factor_any(g: int, xs: Sequence[int], n: int) -> list[int]:
    """:func:`batch_root_factor` 的任意长度版本。

    分治要求长度为 2 的幂，但方案里 ``n`` 是个自由参数（例如 1000 个块），
    所以这里把 ``xs`` 切成「最大的 2 的幂 + 余下部分」两段，分别递归：

    设 ``xs = A ++ B``、``P_A = ∏A``、``P_B = ∏B``、``X = P_A · P_B``。
    对 ``i ∈ A`` 有 ``g^{X/x_i} = (g^{P_B})^{P_A/x_i}``，
    对 ``i ∈ B`` 有 ``g^{X/x_i} = (g^{P_A})^{P_B/x_i}`` ——
    两段各自变成一个「换底数」的同型子问题。余下部分可能仍不是 2 的幂，
    于是递归下去，最坏多 log 层。
    """
    m = len(xs)
    if m == 0:
        return []
    if m & (m - 1) == 0:  # 2 的幂
        return batch_root_factor(g, xs, n)

    half = 1 << (m.bit_length() - 1)  # 严格小于 m 的最大 2 的幂
    left, right = list(xs[:half]), list(xs[half:])
    prod_left = product_tree(left)
    prod_right = product_tree(right)

    res = batch_root_factor(pow(g, prod_right, n), left, n)
    res.extend(batch_root_factor_any(pow(g, prod_left, n), right, n))
    return res


def _root_factor_rec(g: int, xs: list[int], chunk: int, n: int) -> list[int]:
    m = len(xs)
    if m == chunk:
        # 整块内所有 xs 都被「除掉」了，指数为 x/x == 1
        return [g % n]

    half = m // 2
    x_left = xs[:half]
    x_right = xs[half:]

    # 论文写法：左半边的基取 g^(右半边全体之积)，右半边对称。
    # 这样递归到叶子时，指数里恰好把「除自己那一块之外」全乘进去了。
    g_left = pow(g, prod(x_right), n)
    g_right = pow(g, prod(x_left), n)

    res = _root_factor_rec(g_left, x_left, chunk, n)
    res.extend(_root_factor_rec(g_right, x_right, chunk, n))
    return res


def _check_power_of_two(m: int) -> None:
    if m <= 0 or (m & (m - 1)) != 0:
        raise ValueError(f"长度必须是 2 的幂，收到 {m}")
