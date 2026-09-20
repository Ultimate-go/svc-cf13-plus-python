"""论文 §4.2 的「带预处理的提交与打开」：``VC.PPCom`` / ``VC.FastOpen``。

朴素做法要把整个向量读一遍才能打开任意子集，代价 O(n)。§4.2 的思路是
**先花钱、后省时间**：预处理阶段把向量切成 ⌈n/B⌉ 个定长块，为每块各算一份
子向量证明并留作建议；在线打开时只碰 ``I`` 落在的那几块。

预处理（Fig. 2）::

    VC.PPCom(crs, B, v):
        (C, aux) ← VC.Com(crs, v)
        π*       ← VC.Open(crs, [n], v, aux)
        π⃗        ← VC.DisaggOneToMany(crs, B, [n], v, π*)
        aux*     := (π_1, ..., π_{n'}, v)
        return C, aux*

在线打开::

    VC.FastOpen(crs, B, aux*, I):
        P_j := {(j-1)B + i : i ∈ [B]}
        S   := 覆盖 I 的最小块下标集
        for j ∈ S:  I_j ← I ∩ P_j;  π'_j ← VC.Disagg(crs, P_j, v_{P_j}, π_j, I_j)
        return VC.AggManyToOne(crs, ((I_j, v_{I_j}, π'_j))_{j∈S})

代价
----
* 建议存储：⌈n/B⌉ · |π| = ⌈n/B⌉ · 2|G|，即论文的 (n/B)·p(λ) 位；
* ``PPCom``：一次 ``Com`` + 一次 ``Open`` + 一次 ``DisaggOneToMany``；
* ``FastOpen``：|S| ≤ min(|I|, ⌈n/B⌉) 次 ``Disagg``（每个 I_j 之和为 |I|）
  加一次 ``AggManyToOne``。逐项都不含 n，所以 **B 越大越快、建议越大**。

B = 1 时每个 P_j 是单点，``Disagg`` 那步可跳过（``I_j = P_j``），
退化成一次性预计算全部 n 个单项证明。

说明：本模块只做「块划分 + 选取 + 分发到 Disagg/AggManyToOne」这层调度，
密码学部分全部复用 :mod:`svc.scheme`。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .scheme import (
    agg_many_to_one,
    commit,
    disagg,
    disagg_one_to_many,
    open_subvector,
)
from .types import CRSn, Opening, as_index_set

__all__ = [
    "Precomputed",
    "blocks_of",
    "covering_blocks",
    "ppcom",
    "fast_open",
]


@dataclass(frozen=True)
class Precomputed:
    """``aux*``：预处理产出的建议，交给后续的 :func:`fast_open` 使用。

    :param B: 块大小
    :param n: 向量长度
    :param values: 原始向量（``aux*`` 里本来就带着它）
    :param proofs: 每块的证明 ``π_j``，第 j 项对应下标区间 ``[jB, (j+1)B)``
    """

    B: int
    n: int
    values: tuple[int, ...]
    proofs: tuple[Opening, ...]

    @property
    def n_blocks(self) -> int:
        return len(self.proofs)

    @property
    def block_size(self) -> int:
        return self.B

    @property
    def advice_bits(self) -> int:
        """建议本身的位长，用于对照论文的 ``(n/B)·p(λ)``。"""
        if not self.proofs:
            return 0
        p = self.proofs[0]
        return (p.S_I.bit_length() + p.Lambda_I.bit_length()) * self.n_blocks

    def block_of(self, i: int) -> int:
        """下标 ``i`` 落在第几块。"""
        return i // self.B

    def block_indices(self, j: int) -> tuple[int, ...]:
        """第 ``j`` 块覆盖的下标（末块可能不满）。"""
        lo = j * self.B
        return tuple(range(lo, min(lo + self.B, self.n)))


def blocks_of(n: int, B: int) -> list[tuple[int, ...]]:
    """把 ``[n]`` 切成 ⌈n/B⌉ 个连续块，末块可能短于 B。"""
    if B <= 0:
        raise ValueError("块大小 B 必须为正")
    if n <= 0:
        raise ValueError("向量长度 n 必须为正")
    return [tuple(range(s, min(s + B, n))) for s in range(0, n, B)]


def covering_blocks(I: Sequence[int], B: int) -> list[int]:
    """覆盖 ``I`` 的**最小**块下标集 ``S``。

    块划分是「每个下标恰好属于一块」，所以含 ``I`` 中各下标的块一个都不能省，
    取 ``{i // B}`` 即为最小。
    """
    if B <= 0:
        raise ValueError("块大小 B 必须为正")
    return sorted({int(i) // B for i in I})


def ppcom(
    crs_n: CRSn,
    B: int,
    vals: Sequence[int],
    *,
    use_batch: bool = True,
) -> tuple[int, Precomputed]:
    """``VC.PPCom`` —— 提交并生成预处理建议。

    :param B: 块大小
    :param vals: 向量
    :returns: ``(C, aux*)``

    第 2 步的 ``π* = VC.Open(crs, [n], v)`` 在本方案里恒为 ``(g, 1)``：
    :math:`S_{[n]} = g^{e_{[n]}/e_{[n]}} = g`，:math:`\\Lambda_{[n]} = 1`
    （空集上无值可累）。所以它只是个形式上的中间量，不携带信息 ——
    真正的工作量在第 3 步的 ``DisaggOneToMany``。
    """
    n = len(vals)
    if n <= 0:
        raise ValueError("向量不能为空")
    if B > n:
        raise ValueError(f"块大小 B={B} 超过向量长度 n={n}")

    C = commit(crs_n, vals, use_batch=use_batch).C

    all_idx = list(range(n))
    pi_all = open_subvector(crs_n, all_idx, vals, vals, use_batch=use_batch)
    split = disagg_one_to_many(crs_n, B, all_idx, vals, pi_all)

    proofs = tuple(p for _, _, p in split)
    return C, Precomputed(B=B, n=n, values=tuple(vals), proofs=proofs)


def fast_open(
    crs_n: CRSn,
    aux: Precomputed,
    I: Sequence[int],
    *,
    use_batch: bool = True,
) -> Opening:
    """``VC.FastOpen`` —— 用预处理建议快速打开子集 ``I``。

    :param aux: :func:`ppcom` 的输出
    :param I: 要打开的下标集合
    :returns: :class:`~svc.Opening`，可直接交给 :func:`svc.verify`

    :raises ValueError: ``I`` 越界或为空。
    """
    I_set = as_index_set(I)
    if not I_set:
        raise ValueError("打开的下标集合不能为空")
    if I_set[-1] >= aux.n:
        raise ValueError(f"下标 {I_set[-1]} 越界（长度 {aux.n}）")

    parts: list[tuple[tuple[int, ...], tuple[int, ...], Opening]] = []
    for j in covering_blocks(I_set, aux.B):
        P_j = aux.block_indices(j)
        lo = j * aux.B
        I_j = tuple(i for i in I_set if lo <= i < lo + aux.B)
        v_Pj = tuple(aux.values[i] for i in P_j)
        v_Ij = tuple(aux.values[i] for i in I_j)

        if len(I_j) == len(P_j):
            pi_j = aux.proofs[j]
        else:
            pi_j = disagg(crs_n, P_j, v_Pj, aux.proofs[j], I_j)
        parts.append((I_j, v_Ij, pi_j))

    if len(parts) == 1:
        return parts[0][2]
    return agg_many_to_one(crs_n, parts)
