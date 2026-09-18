"""方案用到的数据结构。

全部用 ``@dataclass`` + 冻结 ``tuple`` 表示，理由：

* **可比较 / 可序列化**：测试里要断言两次计算得到的东西完全相等，
  用 ``==`` 即可；JSON 序列化也直接可用。
* **不含大整数的 repr**：``N``、``C``、``S_I`` 都是几千位的整数，
  默认 ``repr`` 会把终端刷爆，所以统一覆写成「位长 + 摘要」形式。
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from enum import IntEnum
from typing import NamedTuple, Sequence

from .primegen import PrimeGen, PrimeGenHash

__all__ = [
    "CRS",
    "CRSn",
    "VectorDigest",
    "Commitment",
    "Opening",
    "VerifyCode",
    "VerifyReport",
    "fingerprint",
]


def fingerprint(x: int, hex_chars: int = 8) -> str:
    """给大整数算一个短指纹，用于日志与调试输出。

    做法是 SHA-256 前 ``hex_chars/2`` 字节的十六进制。**不是**密码学摘要，
    只是为了让日志可读、可对比。不要在任何安全相关的地方用它。
    """
    if x is None:
        return "None"
    raw = x.to_bytes((max(x.bit_length(), 1) + 7) // 8, "big")
    return hashlib.sha256(raw).hexdigest()[:hex_chars]


# ---------------------------------------------------------------------------
# CRS
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CRS:
    """``VC.Setup`` 的输出（对应清单 #18）。

    :param N: 隐藏阶群模数
    :param g: 生成元（固定值 :data:`~svc.groups.RSA_DEFAULT_EXPONENT` 归约后）
    :param primegen: 下标 → 素数映射
    :param l: 每个元素的比特数；素数位长为 ``l + 1``
    """

    N: int
    g: int
    primegen: PrimeGen | PrimeGenHash
    l: int

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"CRS(N={self.N.bit_length()}位/{fingerprint(self.N)}, "
            f"g={self.g}, l={self.l}, "
            f"素数映射={type(self.primegen).__name__})"
        )


@dataclass(frozen=True)
class CRSn:
    """``VC.Specialize`` 的输出（对应清单 #19）。

    :param crs: 原始 CRS
    :param U_n: :math:`U_n = g^{e_{[n]}}`，对全体位置的累加器
    :param e_all: :math:`e_{[n]} = \\prod_{i=1}^{n} e_i`

    ``e_all`` 必须一起存下来：验证时重构 :math:`S_i` 要用它，
    算 :math:`S_I`、:math:`\\Lambda_I` 也都要用。漏存会导致每次都要重新连乘 n 个素数。
    """

    crs: CRS
    U_n: int
    e_all: int
    n: int

    @property
    def N(self) -> int:
        return self.crs.N

    @property
    def g(self) -> int:
        return self.crs.g

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"CRSn(n={self.n}, l={self.crs.l}, "
            f"N={self.N.bit_length()}位, "
            f"U_n={fingerprint(self.U_n)}, e_all={self.e_all.bit_length()}位)"
        )


# ---------------------------------------------------------------------------
# 核心抽象：向量摘要
# ---------------------------------------------------------------------------

class VectorDigest(NamedTuple):
    """向量摘要 :math:`d(\\mathbf{v}) = (S, \\Lambda)`。

    .. math::
        S = g^{e_{[n]}}, \\qquad
        \\Lambda = \\prod_{i \\in [n]} \\left(S^{1/e_i}\\right)^{v_i}

    这是整个方案**唯一**的核心对象。关键在于：

    * ``VC.Com`` 返回的就是 :math:`d(\\mathbf{v})` 的 ``Lambda`` 分量
      （``S`` 分量就是 :math:`U_n`，在 ``Specialize`` 阶段已经算好）；
    * ``VC.Open(\\cdot, I)`` 返回的 :math:`\\pi_I`
      **就是「去掉 I 之后那个向量的摘要」**，即
      :math:`\\pi_I = d(\\mathbf{v} \\setminus I)`。

    于是 **commit 与 open 是同一个函数在两个不同 ``excluded`` 下的取值**：

    ==================  ====================  ==============================
    ``excluded``         返回                  含义
    ==================  ====================  ==============================
    :math:`\\varnothing`  :math:`(U_n, C)`      对全向量的摘要（= 承诺）
    :math:`I`             :math:`(S_I, \\Lambda_I)` 对子向量的摘要（= 打开证明）
    ==================  ====================  ==============================

    这条统一视角把「承诺、打开、拆分、聚合」四件事收到同一个概念底下，
    也是 :func:`~svc.scheme.verify` 能写成
    「把 ``I`` 逐个加回去，看是否变回 :math:`d(\\mathbf{v})`」的原因。
    """

    S: int
    Lambda: int

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"VectorDigest(S={fingerprint(self.S)}, Λ={fingerprint(self.Lambda)})"
        )


# ---------------------------------------------------------------------------
# 承诺与打开
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Commitment:
    """``VC.Com`` 的输出（对应清单 #20）。

    :param C: 单个群元素，与向量长度**无关**
    :param aux: 原始向量本身（清单原文：「aux 就是原始数据本身」）。
                打开时要算 :math:`\\Lambda_I = \\prod_{j \\notin I} (S_j^{1/e_I})^{y_j}`，
                指数用得到**所有**位置的值，而不只是 ``I`` 里的。
    """

    C: int
    aux: tuple[int, ...]

    @property
    def size(self) -> int:
        return len(self.aux)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return f"Commitment(size={len(self.aux)}, C={fingerprint(self.C)})"


@dataclass(frozen=True)
class Opening:
    """``VC.Open`` 的输出 :math:`\\pi_I = (S_I, \\Lambda_I)`（对应清单 #21）。

    **两个群元素，与向量长度和打开个数都无关** —— 这就是 succinct 的含义。

    :param S_I: :math:`S_I = g^{e_{[n]}/e_I}`
    :param Lambda_I: :math:`\\Lambda_I = (\\prod_{j \\notin I} S_j^{y_j})^{1/e_I}`
    :param I: 这组打开对应的下标集合（升序元组）。
              论文里 ``I`` 是 ``Open`` 的输入、不属于 :math:`\\pi_I`；
              这里一并带上是为了让聚合/拆分接口更顺手，比对两个
              :class:`Opening` 相等时也会连下标一起比。
    """

    S_I: int
    Lambda_I: int
    I: tuple[int, ...] = ()

    @property
    def digest(self) -> VectorDigest:
        """以 :class:`VectorDigest` 的视角看待这份证明。

        体现的就是「证明就是摘要」：:math:`\\pi_I = d(\\mathbf{v} \\setminus I)`。
        """
        return VectorDigest(self.S_I, self.Lambda_I)

    @classmethod
    def from_digest(
        cls, d: VectorDigest, I: Sequence[int] = ()
    ) -> "Opening":
        """由摘要 + 下标集合构造一份证明。"""
        return cls(d.S, d.Lambda, as_index_set(I))

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"Opening(I={list(self.I)}, "
            f"S_I={fingerprint(self.S_I)}, Λ_I={fingerprint(self.Lambda_I)})"
        )


# ---------------------------------------------------------------------------
# 验证结果
# ---------------------------------------------------------------------------

class VerifyCode(IntEnum):
    """验证失败的**具体环节**。清单 #22 要求「具体哪一步非真可以返回不同的警告」。"""

    OK = 0
    #: 打开的形状不对（下标越界、重复、长度不匹配）
    BAD_SHAPE = 1
    #: 第一步失败：:math:`S_I^{e_I} \\ne U_n`，说明 :math:`S_I` 是伪造的
    BAD_S_I = 2
    #: 第三步失败：:math:`\\Lambda_I^{e_I} \\cdot \\prod_{i \\in I} S_i^{y_i} \\ne C`
    BAD_LAMBDA = 3


@dataclass(frozen=True)
class VerifyReport:
    """三步验证的结果。

    :param code: 失败环节，:attr:`VerifyCode.OK` 表示全部通过
    :param message: 人话解释，便于前端直接展示
    """

    code: VerifyCode
    message: str = ""

    @property
    def ok(self) -> bool:
        return self.code is VerifyCode.OK

    def __bool__(self) -> bool:
        return self.ok

    @staticmethod
    def success() -> "VerifyReport":
        return VerifyReport(VerifyCode.OK, "验证通过")

    @staticmethod
    def fail(code: VerifyCode, message: str) -> "VerifyReport":
        return VerifyReport(code, message)


# ---------------------------------------------------------------------------
# 便捷构造
# ---------------------------------------------------------------------------

def as_index_set(indices: Sequence[int]) -> tuple[int, ...]:
    """把下标序列规范化成**升序去重元组**。

    聚合/拆分的正确性对下标顺序不敏感，但为了让测试能直接 ``==`` 比较，
    统一规范化能省掉一堆「集合相同但顺序不同」的假失败。
    """
    return tuple(sorted(set(int(i) for i in indices)))
