"""可复现的确定性随机源。

为什么不用标准库 ``random``
---------------------------
基准测试和测试用例都要求「同一个种子必然得到同一组参数、同一个承诺」。
``random.Random`` 的实现（Mersenne Twister）虽然稳定，但 ``randrange``
的取模拒绝策略在不同 Python 版本间**没有跨版本保证**。
本模块用 SHA-256 计数器模式自己实现，输出完全由种子决定，
在任何 Python 版本、任何平台上都一样，便于复现论文里的实验数据。
"""

from __future__ import annotations

import hashlib

__all__ = ["DeterministicRNG"]


class DeterministicRNG:
    """SHA-256 计数器模式的伪随机源。

    :param seed: 种子，可以是 ``bytes`` / ``str`` / ``int``。

    输出流 = ``SHA256(seed || counter)`` 拼接而成，``counter`` 从 0 递增。
    """

    __slots__ = ("_seed", "_counter", "_buf")

    def __init__(self, seed: bytes | str | int = b"python-svc-v1") -> None:
        if isinstance(seed, str):
            seed = seed.encode("utf-8")
        elif isinstance(seed, int):
            length = max(1, (seed.bit_length() + 7) // 8)
            seed = seed.to_bytes(length, "big")
        # 先做一次哈希，避免短种子的结构问题
        self._seed: bytes = hashlib.sha256(seed).digest()
        self._counter: int = 0
        self._buf: bytes = b""

    # -- 底层字节流 ---------------------------------------------------------

    def _refill(self, nbytes: int) -> bytes:
        """保证缓冲区至少有 ``nbytes`` 字节。"""
        while len(self._buf) < nbytes:
            block = hashlib.sha256(
                self._seed + self._counter.to_bytes(8, "big")
            ).digest()
            self._counter += 1
            self._buf += block
        return self._buf

    def read_bytes(self, nbytes: int) -> bytes:
        """取出 ``nbytes`` 字节。"""
        if nbytes < 0:
            raise ValueError("nbytes 不能为负")
        self._refill(nbytes)
        out, self._buf = self._buf[:nbytes], self._buf[nbytes:]
        return out

    # -- 常用随机数接口（与 random.Random 对齐） ---------------------------

    def getrandbits(self, k: int) -> int:
        """返回 ``k`` 位随机非负整数（``k`` 位是**上界**，可能有前导零）。"""
        if k < 0:
            raise ValueError("k 不能为负")
        if k == 0:
            return 0
        nbytes = (k + 7) // 8
        value = int.from_bytes(self.read_bytes(nbytes), "big")
        # 截到恰好 k 位
        return value >> (nbytes * 8 - k)

    def randbelow(self, n: int) -> int:
        """返回 ``[0, n)`` 内的均匀随机整数（拒绝采样，无模偏置）。"""
        if n <= 0:
            raise ValueError("n 必须为正")
        k = (n - 1).bit_length()
        while True:
            r = self.getrandbits(k)
            if r < n:
                return r

    def randrange(self, a: int, b: int) -> int:
        """返回 ``[a, b)`` 内的均匀随机整数。"""
        if a >= b:
            raise ValueError("需要 a < b")
        return a + self.randbelow(b - a)

    def randint(self, a: int, b: int) -> int:
        """返回 ``[a, b]`` 内的均匀随机整数。"""
        return self.randrange(a, b + 1)

    def choice(self, seq):
        return seq[self.randbelow(len(seq))]

    def sample_bits(self, n: int) -> list[int]:
        """返回 ``n`` 个随机比特（0/1）。"""
        return [self.getrandbits(1) for _ in range(n)]
