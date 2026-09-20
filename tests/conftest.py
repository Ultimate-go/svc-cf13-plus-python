"""pytest 共享夹具。

设计原则
--------
* **模数取小**（256~512 位）。测试要验证的是**代数正确性**，不是安全强度；
  512 位模数下所有等式一样成立，但跑得快几十倍。
* **CRS 用 session 级夹具**。生成 RSA 模数是所有操作里最贵的一步，
  每个测试函数重来一遍会让整个套件从几秒变成几分钟。
* **一切用固定种子**。同一个种子必然得到同一组参数，
  失败时能稳定复现。
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# 让 tests/ 能直接 import svc / vds
ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from svc import DeterministicRNG, setup, specialize  # noqa: E402

#: 测试统一使用的元素位长（素数位长 = l + 1 = 17）
L = 16

#: 测试统一使用的向量长度
N = 16

#: 模数位长。256 位足够跑通全部代数关系，且生成只需毫秒级。
MODULUS_BITS = 256


@pytest.fixture(scope="session")
def crs():
    """整个测试会话共用一个 CRS。"""
    rng = DeterministicRNG(b"pytest-crs")
    return setup(lambda_bits=16, l=L, n=N, rng=rng, modulus_bits=MODULUS_BITS)


@pytest.fixture(scope="session")
def crs_n(crs):
    """整个测试会话共用一个 ``crs_n``（即 :math:`U_n`、:math:`e_{[n]}` 已算好）。"""
    return specialize(crs, N)


@pytest.fixture(scope="session")
def values():
    """一组固定的测试向量。"""
    rng = DeterministicRNG(b"pytest-values")
    return tuple(rng.randbelow(1 << L) for _ in range(N))


@pytest.fixture(scope="session")
def committed(crs_n, values):
    """已承诺的 ``(crs_n, Commitment)``。"""
    from svc import commit

    return commit(crs_n, values)
