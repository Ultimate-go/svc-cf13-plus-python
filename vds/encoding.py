"""文件 ↔ 块 的编码。

方案里的「向量」是 :math:`(v_1, \\dots, v_n)`，每个 :math:`v_i` 是 ``l`` 位整数。
本模块负责把任意字节串切成这样的向量，以及反向拼回。

约定
----
* ``l`` 必须是 8 的倍数（``l = 8 * block_bytes``），这样一个块正好 ``block_bytes``
  字节，不会出现跨字节的位对齐问题。
* 文件长度不是块大小整数倍时，**用零补齐**到整数块。
  这是工程上的选择，不是论文的要求；补齐后 :math:`n` 会略大于
  :math:`\\lceil |\\text{file}| / \\text{block\\_bytes} \\rceil`。
  反向拼接时由调用方凭原始长度截断。
"""

from __future__ import annotations

__all__ = ["blocks_for_length", "split_bytes", "join_blocks", "l_for_block_bytes"]


def l_for_block_bytes(block_bytes: int) -> int:
    """由「每块字节数」推出方案参数 ``l``。

    ``l = 8 · block_bytes``，因此 :math:`v_i \\in [0, 2^l)` 恒成立。
    """
    if block_bytes <= 0:
        raise ValueError("block_bytes 必须为正")
    return 8 * block_bytes


def blocks_for_length(total_bytes: int, block_bytes: int) -> int:
    """算出一个 ``total_bytes`` 字节的文件会被切成多少块（向上取整）。"""
    if total_bytes < 0:
        raise ValueError("total_bytes 不能为负")
    if block_bytes <= 0:
        raise ValueError("block_bytes 必须为正")
    if total_bytes == 0:
        return 0
    return (total_bytes + block_bytes - 1) // block_bytes


def split_bytes(data: bytes, block_bytes: int) -> list[int]:
    """把字节串切成 ``n`` 个 ``block_bytes`` 字节的块，每块作为一个整数。

    :returns: 长度 ``n`` 的整数列表，每个元素 :math:`< 2^{8 \\cdot block\\_bytes}`
    """
    if block_bytes <= 0:
        raise ValueError("block_bytes 必须为正")
    if len(data) == 0:
        return []

    n = blocks_for_length(len(data), block_bytes)
    padded = data + b"\x00" * (n * block_bytes - len(data))

    return [
        int.from_bytes(padded[i * block_bytes : (i + 1) * block_bytes], "big")
        for i in range(n)
    ]


def join_blocks(blocks, block_bytes: int, total_bytes: int | None = None) -> bytes:
    """把块拼回字节串。

    :param total_bytes: 原始文件长度。给了就在末尾截断，
                        以去掉 :func:`split_bytes` 补的零。
    """
    if block_bytes <= 0:
        raise ValueError("block_bytes 必须为正")

    raw = b"".join(
        int(v).to_bytes(block_bytes, "big") for v in blocks
    )
    if total_bytes is not None:
        if total_bytes > len(raw):
            raise ValueError(
                f"原始长度 {total_bytes} 超过了拼回来的 {len(raw)} 字节，数据不完整"
            )
        raw = raw[:total_bytes]
    return raw
