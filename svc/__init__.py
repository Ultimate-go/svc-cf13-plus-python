<<<<<<< HEAD
"""python_SVC_v1 —— 第二个 SVC 方案（论文 §5.2）的纯 Python 实现。

对应论文
--------
ASIACRYPT 2020, *Incrementally Aggregatable Vector Commitments and
Applications to Verifiable Decentralized Storage*, **§5.2**。
基于 CF13 / LM19 的 RSA 型向量承诺，加上两个技术贡献：

1. 公开参数与验证时间**与向量长度无关**（原来的 ``S_1..S_n`` 被换成
   ``U_n`` 加一次 ``S_I^{e_I} = U_n`` 的校验）；
2. 给出了**增量聚合/拆分**算法，使打开证明可以任意顺序、任意次数合并。

模块导航
--------
======================  ==================================================
模块                    内容（对应清单编号）
======================  ==================================================
:mod:`svc.mathbase`     数学底座（#1~#8）
:mod:`svc.groups`       隐藏阶群生成（#9）
:mod:`svc.primegen`     下标→素数映射（#10、#11）
:mod:`svc.scheme`       方案中间量 + 本体 + 聚合拆分（#12~#26）
:mod:`svc.fastopen`     §4.2 预处理提交与快速打开（``PPCom``/``FastOpen``）
:mod:`svc.yinyan`       §5.1 阴阳方案（双累加器 SVC）
:mod:`svc.pok`          §6 知识论证（``PoProd2``/``PoProd*``/``PoKOpen``/``PoKSubV``）
:mod:`svc.rng`          可复现随机源
:mod:`svc.types`        数据结构
======================  ==================================================

最小用法
--------
::

    from svc import DeterministicRNG, setup, specialize, commit, open_subvector, verify

    rng = DeterministicRNG(b"demo")
    crs = setup(lambda_bits=128, l=8, n=16, rng=rng)
    crs_n = specialize(crs, 16)

    vals = [rng.randbelow(1 << 8) for _ in range(16)]
    com = commit(crs_n, vals)

    I = [2, 5, 7]
    pi = open_subvector(crs_n, I, [vals[i] for i in I], vals)
    assert verify(crs_n, com.C, I, [vals[i] for i in I], pi)

.. note::

   ``open_subvector`` 就是清单 #21 里的 ``open``。
   因为 ``open`` 是 Python 内置函数，包顶层不用这个名字导出，
   但 ``svc.scheme.open(...)`` 这个别名依然可用。

.. note::

   §5.1 与 §6 的两套接口**不在包顶层导出** ——
   它们的 ``setup`` / ``commit`` / ``verify`` 与 §5.2 同名但含义不同，
   混在一起会让人分不清用的是哪一套。需要时请显式引入：
   ``from svc.yinyan import setup1, commit1, ver1``、
   ``from svc.pok import poksubv_prove, poksubv_verify``。
   依赖它们的 ``VDS1`` 在 :mod:`vds.vds1`。
"""

from __future__ import annotations

from .groups import (
    MIN_MODULUS_BITS,
    RSA_DEFAULT_EXPONENT,
    HiddenOrderGroup,
    gen_prime,
    generate_primes,
)
from .mathbase import (
    batch_root_factor,
    batch_root_factor_any,
    batch_root_factor_general,
    egcd,
    group_div,
    hash_prime,
    is_probable_prime,
    mod_inverse,
    multiexp,
    next_prime,
    prod,
    product_tree,
    shamir_trick,
    weighted_root_product,
)
from .primegen import PrimeGen, PrimeGenHash, is_probable_prime_screened
from .rng import DeterministicRNG
from .fastopen import (
    Precomputed,
    blocks_of,
    covering_blocks,
    fast_open,
    ppcom,
)
from .scheme import (
    DEFAULT_MODULUS_BITS,
    add_back,
    agg,
    agg_many_to_one,
    commit,
    digest_of,
    disagg,
    disagg_one_to_many,
    e_of,
    lambda_subset,
    multi_exponentiate,
    open_subvector,
    reconstruct_s_i,
    s_iota,
    s_partial_root,
    s_subset,
    setup,
    specialize,
    verify,
)
from .types import (
    CRS,
    CRSn,
    Commitment,
    Opening,
    VectorDigest,
    VerifyCode,
    VerifyReport,
    as_index_set,
    fingerprint,
)

__version__ = "1.0.0"

__all__ = [
    "__version__",
    # groups
    "MIN_MODULUS_BITS",
    "RSA_DEFAULT_EXPONENT",
    "HiddenOrderGroup",
    "gen_prime",
    "generate_primes",
    # mathbase
    "is_probable_prime",
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
    # primegen
    "PrimeGen",
    "PrimeGenHash",
    "is_probable_prime_screened",
    # rng
    "DeterministicRNG",
    # scheme
    "DEFAULT_MODULUS_BITS",
    "VectorDigest",
    "digest_of",
    "add_back",
    "e_of",
    "s_iota",
    "s_subset",
    "s_partial_root",
    "reconstruct_s_i",
    "lambda_subset",
    "multi_exponentiate",
    "setup",
    "specialize",
    "commit",
    "open_subvector",
    "verify",
    "disagg",
    "agg",
    "disagg_one_to_many",
    "agg_many_to_one",
    # fastopen (§4.2)
    "Precomputed",
    "blocks_of",
    "covering_blocks",
    "ppcom",
    "fast_open",
    # types
    "CRS",
    "CRSn",
    "VectorDigest",
    "Commitment",
    "Opening",
    "VerifyCode",
    "VerifyReport",
    "as_index_set",
    "fingerprint",
]
=======
"""python_SVC_v1 —— 第二个 SVC 方案（论文 §5.2）的纯 Python 实现。

对应论文
--------
ASIACRYPT 2020, *Incrementally Aggregatable Vector Commitments and
Applications to Verifiable Decentralized Storage*, **§5.2**。
基于 CF13 / LM19 的 RSA 型向量承诺，加上两个技术贡献：

1. 公开参数与验证时间**与向量长度无关**（原来的 ``S_1..S_n`` 被换成
   ``U_n`` 加一次 ``S_I^{e_I} = U_n`` 的校验）；
2. 给出了**增量聚合/拆分**算法，使打开证明可以任意顺序、任意次数合并。

模块导航
--------
======================  ==================================================
模块                    内容（对应清单编号）
======================  ==================================================
:mod:`svc.mathbase`     数学底座（#1~#8）
:mod:`svc.groups`       隐藏阶群生成（#9）
:mod:`svc.primegen`     下标→素数映射（#10、#11）
:mod:`svc.scheme`       方案中间量 + 本体 + 聚合拆分（#12~#26）
:mod:`svc.fastopen`     §4.2 预处理提交与快速打开（``PPCom``/``FastOpen``）
:mod:`svc.rng`          可复现随机源
:mod:`svc.types`        数据结构
======================  ==================================================

最小用法
--------
::

    from svc import DeterministicRNG, setup, specialize, commit, open_subvector, verify

    rng = DeterministicRNG(b"demo")
    crs = setup(lambda_bits=128, l=8, n=16, rng=rng)
    crs_n = specialize(crs, 16)

    vals = [rng.randbelow(1 << 8) for _ in range(16)]
    com = commit(crs_n, vals)

    I = [2, 5, 7]
    pi = open_subvector(crs_n, I, [vals[i] for i in I], vals)
    assert verify(crs_n, com.C, I, [vals[i] for i in I], pi)

.. note::

   ``open_subvector`` 就是清单 #21 里的 ``open``。
   因为 ``open`` 是 Python 内置函数，包顶层不用这个名字导出，
   但 ``svc.scheme.open(...)`` 这个别名依然可用。
"""

from __future__ import annotations

from .groups import (
    MIN_MODULUS_BITS,
    RSA_DEFAULT_EXPONENT,
    HiddenOrderGroup,
    gen_prime,
    generate_primes,
)
from .mathbase import (
    batch_root_factor,
    batch_root_factor_any,
    batch_root_factor_general,
    egcd,
    group_div,
    hash_prime,
    is_probable_prime,
    mod_inverse,
    multiexp,
    next_prime,
    prod,
    product_tree,
    shamir_trick,
    weighted_root_product,
)
from .primegen import PrimeGen, PrimeGenHash, is_probable_prime_screened
from .rng import DeterministicRNG
from .fastopen import (
    Precomputed,
    blocks_of,
    covering_blocks,
    fast_open,
    ppcom,
)
from .scheme import (
    DEFAULT_MODULUS_BITS,
    add_back,
    agg,
    agg_many_to_one,
    commit,
    digest_of,
    disagg,
    disagg_one_to_many,
    e_of,
    lambda_subset,
    multi_exponentiate,
    open_subvector,
    reconstruct_s_i,
    s_iota,
    s_partial_root,
    s_subset,
    setup,
    specialize,
    verify,
)
from .types import (
    CRS,
    CRSn,
    Commitment,
    Opening,
    VectorDigest,
    VerifyCode,
    VerifyReport,
    as_index_set,
    fingerprint,
)

__version__ = "1.0.0"

__all__ = [
    "__version__",
    # groups
    "MIN_MODULUS_BITS",
    "RSA_DEFAULT_EXPONENT",
    "HiddenOrderGroup",
    "gen_prime",
    "generate_primes",
    # mathbase
    "is_probable_prime",
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
    # primegen
    "PrimeGen",
    "PrimeGenHash",
    "is_probable_prime_screened",
    # rng
    "DeterministicRNG",
    # scheme
    "DEFAULT_MODULUS_BITS",
    "VectorDigest",
    "digest_of",
    "add_back",
    "e_of",
    "s_iota",
    "s_subset",
    "s_partial_root",
    "reconstruct_s_i",
    "lambda_subset",
    "multi_exponentiate",
    "setup",
    "specialize",
    "commit",
    "open_subvector",
    "verify",
    "disagg",
    "agg",
    "disagg_one_to_many",
    "agg_many_to_one",
    # fastopen (§4.2)
    "Precomputed",
    "blocks_of",
    "covering_blocks",
    "ppcom",
    "fast_open",
    # types
    "CRS",
    "CRSn",
    "VectorDigest",
    "Commitment",
    "Opening",
    "VerifyCode",
    "VerifyReport",
    "as_index_set",
    "fingerprint",
]
>>>>>>> main
