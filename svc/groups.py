"""隐藏阶群生成 —— 对应 to-do-function-list.txt 第二部分 #9。

方案假设存在隐藏阶群 :math:`\\mathbb{G} \\leftarrow \\mathcal{G}_{gen}(1^\\lambda)`，
其阶未知（这就是「隐藏阶」的含义）。本模块用 RSA 群实例化：

.. math::
    N = p \\cdot q, \\qquad \\mathbb{G} = \\mathbb{Z}_N^{*}

``p``、``q`` 生成后立刻丢弃，**方案运行期间任何人都不知道** ``\\varphi(N)``。
这保证了「求 ``e`` 次根」是困难的（strong RSA 假设），
也保证了 :func:`~svc.mathbase.mod_inverse` 只能用 ``N`` 而不能用群阶 ——
这正是本方案能公开计算 ``S_j`` 的 ``1/e_I`` 次方的原因。
"""

from __future__ import annotations

import math

from .mathbase import is_probable_prime
from .rng import DeterministicRNG

__all__ = [
    "RSA_DEFAULT_EXPONENT",
    "gen_prime",
    "generate_primes",
    "HiddenOrderGroup",
]


#: 固定的生成元 ``g``，取自参考实现 ``rust-yinyan`` 的 ``RSAGroup``。
#: 它同时是 RSA 的公开指数，要求 :math:`\\gcd(g, \\varphi(N)) = 1`
#: （这样 ``g`` 在 :math:`\\mathbb{Z}_N^{*}` 里才不会落入小阶子群）。
RSA_DEFAULT_EXPONENT: int = 65547

#: 最小的可接受模数位长。低于 64 位时 RSA 群没有意义，参考实现直接报错。
MIN_MODULUS_BITS: int = 64


def gen_prime(rng: DeterministicRNG, bits: int) -> int:
    """生成恰好 ``bits`` 位的素数，且**最高两位都是 1**。

    置最高两位的原因：这样 ``p ∈ [3·2^(bits-2), 2^bits)``，
    两个这样的素数相乘时，乘积位长不会比预期短太多，
    让 :func:`generate_primes` 里「乘积必须恰好 bits 位」的检查更容易通过。

    :param bits: 位长，至少 2。
    """
    if bits < 2:
        raise ValueError("bits 至少为 2")

    top_mask = (1 << (bits - 1)) | (1 << (bits - 2))
    while True:
        candidate = rng.getrandbits(bits) | top_mask | 1  # 最高两位 + 最低位都置 1
        if is_probable_prime(candidate):
            return candidate


def generate_primes(
    rng: DeterministicRNG,
    bits: int,
) -> tuple[int, int]:
    """生成隐藏阶群，返回 ``(N, g)``。对应清单 **#9**。

    :param bits: 模数 ``N`` 的位长（例如 2048）。``p``、``q`` 各占一半。
    :returns: ``(N, g)``，其中 ``N = p*q`` 恰好 ``bits`` 位，
              ``g`` 是固定值 :data:`RSA_DEFAULT_EXPONENT` 归约到 ``[1, N)``。

    清单要求的四件事，逐一落实：

    1. **``N = p*q``**，``p``、``q`` 各约 ``bits/2`` 位 —— 见 :func:`gen_prime`。
    2. **``p ≠ q``** —— 相等就重新抽（概率约 :math:`2^{-bits/2}`，实际上永不发生，
       但检查是白送的，留着）。
    3. **``φ(N)`` 生成后即丢弃** —— 局部变量算出后立刻 ``del``，
       函数返回的元组里只有 ``N`` 和 ``g``，调用方拿不到 ``p``、``q``。
    4. **``gcd(g, φ(N)) = 1``** —— 用 ``gcd`` 检查；不满足就换一对 ``p``、``q``。
       清单原文「g 取定值，且要求 g 与 φ(N) 互素」说的就是这件事。

    另外还强制 **``N`` 的位长恰好等于 ``bits``**（参考实现同样有这个检查），
    这样论文里所有以位长表述的复杂度才有意义。

    :raises ValueError: ``bits`` 小于 :data:`MIN_MODULUS_BITS`。
    """
    if bits < MIN_MODULUS_BITS:
        raise ValueError(
            f"模数位长至少 {MIN_MODULUS_BITS}，收到 {bits}"
        )

    bits_p = bits // 2
    bits_q = bits - bits_p

    while True:
        p = gen_prime(rng, bits_p)
        q = gen_prime(rng, bits_q)

        if p == q:  # 要求 p、q 互不相同
            continue

        n = p * q
        if n.bit_length() != bits:  # 乘积必须恰好 bits 位
            continue

        totient = (p - 1) * (q - 1)

        # g 与 φ(N) 必须互素，否则 g 的阶会退化
        if math.gcd(RSA_DEFAULT_EXPONENT, totient) != 1:
            continue

        # 到这里 p、q、φ(N) 全部丢弃：只把 N 和 g 交出去
        del p, q, totient

        g = RSA_DEFAULT_EXPONENT % n  # 归约到 [1, N)
        return n, g


class HiddenOrderGroup:
    """隐藏阶群 :math:`\\mathbb{Z}_N^{*}` 的轻量封装。

    只保存 ``N`` 和 ``g``，**不保存任何阶信息**。所有运算都委托给
    内置三参数 ``pow``。存在的意义是让上层代码不必到处传 ``N``。
    """

    __slots__ = ("N", "g")

    def __init__(self, N: int, g: int) -> None:
        if N <= 1:
            raise ValueError("N 必须大于 1")
        self.N = N
        self.g = g % N

    @classmethod
    def generate(cls, rng: DeterministicRNG, bits: int) -> "HiddenOrderGroup":
        """按清单 #9 生成一个群实例。"""
        N, g = generate_primes(rng, bits)
        return cls(N, g)

    def mul(self, a: int, b: int) -> int:
        """群乘法。"""
        return a * b % self.N

    def prod(self, xs) -> int:
        """连乘（对空序列返回 1）。"""
        acc = 1
        for x in xs:
            acc = acc * x % self.N
        return acc

    def pow(self, a: int, e: int) -> int:
        """模幂。``e`` 必须非负。"""
        if e < 0:
            raise ValueError("指数必须非负；求逆请用 group_div")
        return pow(a, e, self.N)

    def div(self, a: int, b: int) -> int:
        """群除法 :math:`a \\cdot b^{-1}`。"""
        from .mathbase import group_div

        return group_div(a, b, self.N)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"HiddenOrderGroup(N={self.N.bit_length()} 位, g={self.g})"
