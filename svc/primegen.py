"""下标 → 素数的映射 —— 对应 to-do-function-list.txt 第二部分 #10、#11。

方案里每个位置 :math:`i` 必须对应一个**互不相同**的素数 :math:`e_i`。
互异性不是可选项：:func:`~svc.mathbase.shamir_trick` 在
:math:`\\gcd(e_i, e_j) \\ne 1` 时会**静默返回错误结果**（不是崩溃），
是最难查的一类 bug。本模块提供的两种映射里，
:class:`PrimeGen`（双射）天然无碰撞，是正式使用的唯一选择。

关于位长的说明（重要，别踩）
-----------------------------
清单 #10 原文写「从 2 的 bits 次方开始向上扫描取素数并缓存」，
但同一份清单的记号表要求「:math:`e_i` 是第 :math:`i` 个 **(l+1) 比特** 的素数」，
并且说「bits 取 l+1」。这两条只有在起点取 :math:`2^{\\text{bits}-1}`
（即最小的 ``bits`` 位数）时才自洽 —— 若真的从 :math:`2^{\\text{bits}}` 起步，
扫描出来的素数全部是 ``bits+1`` 位，与位长要求矛盾。

论文 §5.2 明确写的是 "``n`` ``(ℓ+1)``-bit primes"，所以本实现以**位长**为准：
``bits`` 参数就是输出素数的位长，起点为 :math:`2^{\\text{bits}-1}`。
"""

from __future__ import annotations

import math
from functools import reduce
from operator import mul

from .mathbase import hash_prime, is_probable_prime

__all__ = ["PrimeGen", "PrimeGenHash", "is_probable_prime_screened"]


# ---------------------------------------------------------------------------
# 快速素性预筛
# ---------------------------------------------------------------------------

#: 预筛用的小素数上界。取 10000 时，随机候选数被一次 gcd 刷掉的概率约 88%。
_SCREEN_LIMIT: int = 10_000

_SCREEN_PRODUCT: int | None = None


def _primes_upto(limit: int) -> list[int]:
    """埃拉托斯特尼筛，返回 ``[2, limit]`` 内的所有素数。"""
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(limit + 1) if sieve[i]]


def _screen_product() -> int:
    """惰性构造「小于 :data:`_SCREEN_LIMIT` 的所有素数之积」。

    用一次 ``math.gcd``（纯 C 实现）就能把绝大部分合数筛掉，
    比在 Python 里逐个试除快两个数量级。素数生成是本方案**唯一**的热点，
    这个优化能把 10 万级规模的预处理从「不可用」拉到「可接受」。
    """
    global _SCREEN_PRODUCT
    if _SCREEN_PRODUCT is None:
        _SCREEN_PRODUCT = reduce(mul, _primes_upto(_SCREEN_LIMIT), 1)
    return _SCREEN_PRODUCT


def is_probable_prime_screened(n: int) -> bool:
    """:func:`~svc.mathbase.is_probable_prime` 的加速版：先做小因子预筛。

    对 ``n <= _SCREEN_LIMIT`` 直接走原函数（否则小素数自己会被误判为合数）。
    在素数生成这种「大量候选、绝大多数是合数」的场景下，
    一次 gcd 就能砍掉约 88% 的候选，剩下 12% 才进入 Miller-Rabin。
    """
    if n <= _SCREEN_LIMIT:
        return is_probable_prime(n)
    if math.gcd(n, _screen_product()) != 1:
        return False
    return is_probable_prime(n)


# ---------------------------------------------------------------------------
# 10. PrimeGen —— 双射版（正式使用）
# ---------------------------------------------------------------------------

class PrimeGen:
    """下标到素数的**双射**映射。对应清单 **#10**。

    第 ``i`` 个素数（``i`` 从 0 开始）= 从 :math:`2^{\\text{bits}-1}` 起
    向上数第 ``i+1`` 个 ``bits`` 位素数。

    :param max_sz: 最多需要多少个素数（即向量长度 ``n``）
    :param bits: 素数的位长，方案里取 ``l + 1``
    :param start: 起始扫描位置，``None`` 表示 :math:`2^{\\text{bits}-1}`

    .. warning::

       **``n`` 不能超过该位长下素数的总数**。区间
       :math:`[2^{\\text{bits}-1}, 2^{\\text{bits}})` 内只有
       :math:`\\pi(2^{\\text{bits}}) - \\pi(2^{\\text{bits}-1})` 个素数，
       例如 ``l = 4``（5 位素数）时全区间只有 5 个，``n = 8`` 根本不够。
       一旦扫描越过 :math:`2^{\\text{bits}}`，本类会**直接抛异常**，
       而不是悄悄返回位长超标的素数 —— 后者会让论文里所有基于位长的
       安全性分析失效，且极难在测试中被发现。
       做小规模调试时请把 ``l`` 取大一些（``l = 16`` 时可用素数有 5000 多个）。

    为什么是双射就够了
    ------------------
    论文明确说这个映射**不需要**随机预言机的性质，
    「even just a bijective mapping (which is inherently collision resistant)
    would be enough」—— 单调递增的素数序列是单射，
    所以两个不同下标必然得到两个不同素数，**不需要额外做碰撞检查**。

    惰性求值
    --------
    初始化只记录起点，用到哪个下标才算到哪。``n = 2^20`` 时若一次性算完
    要几十秒，而调试阶段往往只需要前几个，惰性求值让调试几乎零成本。
    """

    __slots__ = ("_max_sz", "_bits", "_cache", "_next_candidate")

    def __init__(
        self,
        max_sz: int,
        bits: int,
        start: int | None = None,
    ) -> None:
        if max_sz <= 0:
            raise ValueError("max_sz 必须为正")
        if bits < 3:
            raise ValueError("bits 至少为 3（否则凑不出 bits 位素数）")

        self._max_sz = max_sz
        self._bits = bits
        self._cache: list[int] = []

        if start is None:
            start = 1 << (bits - 1)  # 最小的 bits 位数
        if start < 2:
            start = 2
        self._next_candidate = start | 1  # 从奇数开始，偶数（除 2）不可能是素数

    # -- 惰性扩展 -----------------------------------------------------------

    def _extend(self, count: int) -> None:
        """把缓存扩展到至少 ``count`` 个素数。"""
        if count > self._max_sz:
            raise IndexError(
                f"PrimeGen 只申请了 {self._max_sz} 个素数，被要求第 {count} 个"
            )
        cache = self._cache
        cand = self._next_candidate
        limit = 1 << self._bits
        while len(cache) < count:
            if cand >= limit:
                # 越过 2^bits 之后找到的都是 (bits+1) 位素数，
                # 违背论文「所有 e_i 都是 (l+1) 比特」的前提。
                # 宁可报错，也不要用错位长的素数继续算 —— 那会让安全性分析失效。
                raise ValueError(
                    f"{self._bits} 位素数已经用尽：扫到 2^{self._bits} 只找到 "
                    f"{len(cache)} 个，但需要 {count} 个。"
                    f"请把 l 调大（素数位长 = l+1，越大素数越密）或把 n 调小。"
                )
            if is_probable_prime_screened(cand):
                cache.append(cand)
            cand += 2
        self._next_candidate = cand

    # -- 对外接口 -----------------------------------------------------------

    def get(self, i: int) -> int:
        """取第 ``i`` 个素数（0 基）。对应 ``PrimeHash::get``。"""
        if i < 0 or i >= self._max_sz:
            raise IndexError(f"下标 {i} 越界（容量 {self._max_sz}）")
        if i >= len(self._cache):
            # 每次至少多算一批，避免逐个数地反复触发循环开销
            self._extend(max(i + 1, min(self._max_sz, len(self._cache) * 2 or 8)))
        return self._cache[i]

    def get_many(self, indices) -> list[int]:
        """批量取，一次把缓存扩到位，比逐个 ``get`` 快。"""
        indices = list(indices)
        if not indices:
            return []
        target = max(indices) + 1
        if target > len(self._cache):
            self._extend(target)
        return [self._cache[i] for i in indices]

    def first(self, count: int) -> list[int]:
        """取前 ``count`` 个素数，返回列表。这是 ``specialize`` 的主路径。"""
        if count > len(self._cache):
            self._extend(count)
        return self._cache[:count]

    @property
    def bits(self) -> int:
        return self._bits

    @property
    def max_sz(self) -> int:
        return self._max_sz

    @property
    def computed(self) -> int:
        """已经算出并缓存的素数个数。"""
        return len(self._cache)

    def __getitem__(self, i: int) -> int:
        return self.get(i)

    def __len__(self) -> int:
        return self._max_sz

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"PrimeGen(max_sz={self._max_sz}, bits={self._bits}, "
            f"已缓存={len(self._cache)})"
        )


# ---------------------------------------------------------------------------
# 11. PrimeGenHash —— 哈希版（对照用，禁止正式使用）
# ---------------------------------------------------------------------------

class PrimeGenHash:
    """哈希版素数映射。对应清单 **#11**（可选，仅作对照）。

    :param max_sz: 最多需要多少个素数
    :param prime_bytes: 哈希输出的字节数，决定素数量级

    .. danger::

       **必须检查素数互异性**（清单原文：「必须检查素数互异性，
       位数太小时会碰撞，碰撞会破坏后面的互素性」）。

       本类默认开启 ``check_distinct=True``，一旦发现碰撞**立刻抛异常**，
       而不是把错误带进后续计算。这是刻意的设计：
       碰撞导致的 :func:`~svc.mathbase.shamir_trick` 失败会表现为
       「聚合结果偶尔不对」，几乎不可能靠读代码定位。

       正式跑实验请用 :class:`PrimeGen`（双射天然无碰撞）。
    """

    __slots__ = ("_max_sz", "_prime_bytes", "_cache", "_seen", "_check_distinct")

    def __init__(
        self,
        max_sz: int,
        prime_bytes: int = 16,
        check_distinct: bool = True,
    ) -> None:
        if max_sz <= 0:
            raise ValueError("max_sz 必须为正")
        if prime_bytes < 1:
            raise ValueError("prime_bytes 必须为正")
        self._max_sz = max_sz
        self._prime_bytes = prime_bytes
        self._cache: list[int] = []
        self._seen: dict[int, int] = {}
        self._check_distinct = check_distinct

    def get(self, i: int) -> int:
        """把下标写成 8 字节大端再哈希成素数。"""
        if i < 0 or i >= self._max_sz:
            raise IndexError(f"下标 {i} 越界（容量 {self._max_sz}）")
        while len(self._cache) <= i:
            idx = len(self._cache)
            prime = hash_prime(idx.to_bytes(8, "big"), self._prime_bytes)
            if self._check_distinct:
                if prime in self._seen:
                    raise ValueError(
                        f"哈希版素数映射发生碰撞：下标 {self._seen[prime]} 与 {idx} "
                        f"都映射到 {prime}（prime_bytes={self._prime_bytes} 太小）。"
                        f"请改用 PrimeGen（双射），或增大 prime_bytes。"
                    )
                self._seen[prime] = idx
            self._cache.append(prime)
        return self._cache[i]

    def first(self, count: int) -> list[int]:
        if count:
            self.get(count - 1)
        return self._cache[:count]

    @property
    def max_sz(self) -> int:
        return self._max_sz

    @property
    def computed(self) -> int:
        return len(self._cache)

    def __getitem__(self, i: int) -> int:
        return self.get(i)

    def __len__(self) -> int:
        return self._max_sz

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"PrimeGenHash(max_sz={self._max_sz}, "
            f"prime_bytes={self._prime_bytes}, 已缓存={len(self._cache)})"
        )
