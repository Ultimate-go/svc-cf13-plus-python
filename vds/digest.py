"""VDS 的摘要与本地视图。

论文 §8.2 对 VDS2 的结构约定::

    δ := ((U, C), n)        ← 摘要（digest），客户端只保存它
    st := π_I := (S_I, Λ_I) ← 存储节点的本地状态（state）

其中把 ``U`` 一起放进摘要，是 §8.2 解决「specialize 阶段无法可信生成」这个
难点的关键手法。论文原文：

    U depends on the current size of the file (though not on its content),
    meaning that normally at each addition (or deletion) to the file it
    should be updated. To solve this problem, we attach U to the VDS's
    digest (together with n for technical reasons).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from svc.types import Opening, fingerprint

__all__ = ["Digest", "LocalView"]


@dataclass(frozen=True)
class Digest:
    """文件摘要 :math:`\\delta = ((U, C), n)`。

    :param U: :math:`U_n = g^{e_{[n]}}`，对**全体位置**的累加器。
              注意它不是常量：文件增删位置时 ``U`` 会跟着变，
              所以必须挂在摘要上，而不是放在公开参数 ``pp`` 里。
    :param C: 承诺 :math:`C = \\prod_i S_i^{v_i}`。**单个群元素**。
    :param n: 当前文件被分成的块数。

    客户端只需要保存这**一个**摘要（两个群元素 + 一个整数），
    就能验证任意子集的检索结果 —— 这是整个 VDS 的意义所在。
    """

    U: int
    C: int
    n: int

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"Digest(n={self.n}, U={fingerprint(self.U)}, C={fingerprint(self.C)})"
        )


@dataclass
class LocalView:
    """存储节点的本地视图 ``(pp, δ, n, st, I, FI)``。

    论文的 VDS1 正确性证明里给了一个很有用的判据：

        a local view of a storage node ``(pp, δ, n, st, I, FI)`` is valid
        if :math:`st_1^{a_I} = \\delta_1 \\wedge st_2^{b_I} = \\delta_2`

    换成方案 §5.2 的记号就是：:math:`S_I^{e_I} = U_n` 且
    :math:`\\Lambda_I^{e_I} \\cdot \\prod_{i \\in I} S_i^{F_i} = C` ——
    **正好就是 :func:`svc.verify` 的两步校验**。
    也就是说：「某个存储节点确实老老实实存着它声称的那部分数据」
    这件事，可以用同一个 :func:`svc.verify` 直接检查。
    见 :meth:`~vds.storage_node.StorageNode.check_local_view`。
    """

    delta: Digest
    st: Opening
    I: tuple[int, ...] = ()
    FI: tuple[int, ...] = ()

    @property
    def n(self) -> int:
        return self.delta.n

    def value_of(self, i: int) -> int:
        """取下标 ``i`` 的值；不在本地视图里则抛 ``KeyError``。"""
        try:
            pos = self.I.index(i)
        except ValueError:
            raise KeyError(f"本节点不持有下标 {i}") from None
        return self.FI[pos]

    def has(self, indices) -> bool:
        """是否持有全部给定下标。"""
        held = set(self.I)
        return all(i in held for i in indices)

    def __repr__(self) -> str:  # pragma: no cover - 仅调试用
        return (
            f"LocalView(n={self.n}, |I|={len(self.I)}, "
            f"I={list(self.I[:8])}{'...' if len(self.I) > 8 else ''})"
        )
