"""零依赖的演示后端。

为什么用标准库 ``http.server`` 而不是 FastAPI
--------------------------------------------
整个项目（``svc`` + ``vds``）到目前为止**零第三方依赖**。
演示后端如果引入 FastAPI，就把「跑起来」这件事和「装对包」绑在一起了 ——
而演示恰恰是最不该出环境问题的地方。
:class:`http.server.ThreadingHTTPServer` 完全够用：一个路由表 + JSON 收发，
150 行以内搞定，而且 ``python server/app.py`` 一定能跑起来。

启动::

    python server/app.py            # 默认 http://127.0.0.1:8000
    python server/app.py --port 9000

接口一览（全部 POST + JSON）
----------------------------
==================  ==================================================
路径                 作用
==================  ==================================================
``/api/setup``      建立 VDS 会话（Bootstrap）
``/api/commit``     把文本切成块并承诺
``/api/distribute`` 把块分发到 k 台模拟服务器
``/api/retrieve``   跨服务器检索若干块，收集凭证
``/api/aggregate``  把多份凭证聚合成一个
``/api/verify``     用摘要验证那一个凭证
``/api/attack``     制造攻击（篡改内容 / 伪造证据）
``/api/full``       一键跑完整条流水线
``/api/status``     查看当前状态
==================  ==================================================

.. warning::

   这是**演示用**后端：状态全在进程内存里，没有认证，没有并发保护。
   它的价值是把算法每一步的输入输出和耗时暴露出来，
   不是一个可以部署的存储服务。
"""

from __future__ import annotations

import argparse
import json
import sys
import threading
import time
import traceback
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from svc import DeterministicRNG, Opening, fingerprint  # noqa: E402
from vds import LocalView, StorageNode, VDSSession, join_blocks  # noqa: E402

WEB_DIR = ROOT / "web"

# ---------------------------------------------------------------------------
# 演示状态
# ---------------------------------------------------------------------------


class DemoState:
    """一次演示的全部状态。**不是线程安全的**，用锁串起来。"""

    def __init__(self) -> None:
        self.lock = threading.RLock()
        self.reset()

    def reset(self) -> None:
        self.session: VDSSession | None = None
        self.delta = None
        self.crs_n = None
        self.values: tuple[int, ...] = ()
        self.payload: bytes = b""
        self.block_bytes: int = 16
        self.nodes: list[StorageNode] = []
        self.certs: list = []
        self.pi_K: Opening | None = None
        self.attack: str = "none"

    # -- 序列化辅助 ------------------------------------------------------

    @staticmethod
    def num(x: int) -> dict:
        """把大整数压缩成前端能显示的形式。"""
        return {
            "bits": x.bit_length(),
            "hex": hex(x),
            "fp": fingerprint(x),
        }


STATE = DemoState()


# ---------------------------------------------------------------------------
# 进度
# ---------------------------------------------------------------------------

class Progress:
    """粗粒度的阶段进度，供前端在长任务期间轮询。

    单独一把锁：业务状态那把锁在整个请求期间都被占着，
    轮询接口不能去等它，否则进度查询会被长任务饿死。
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._reset()

    def _reset(self) -> None:
        self._running = False
        self._phase = ""
        self._done = 0
        self._total = 0
        self._detail = ""
        self._t0 = 0.0
        self._elapsed_ms = 0.0
        self._history: list[dict] = []

    def clear(self) -> None:
        with self._lock:
            self._reset()

    def begin(self, phase: str, total: int = 0, detail: str = "") -> None:
        with self._lock:
            self._running = True
            self._phase = phase
            self._done, self._total = 0, total
            self._detail = detail
            self._t0 = time.perf_counter()

    def tick(self, done: int, total: int | None = None, detail: str | None = None) -> None:
        with self._lock:
            self._done = done
            if total is not None:
                self._total = total
            if detail is not None:
                self._detail = detail

    def finish(self) -> None:
        """结束当前阶段。**幂等** —— 成功、失败、异常路径都该调它。"""
        with self._lock:
            if not self._running:
                return
            self._elapsed_ms = (time.perf_counter() - self._t0) * 1000.0
            self._history.append({"phase": self._phase, "ms": round(self._elapsed_ms, 1)})
            self._running = False
            self._done = self._total or self._done
            self._detail = ""

    def snapshot(self) -> dict:
        with self._lock:
            elapsed = self._elapsed_ms
            if self._running:
                elapsed = (time.perf_counter() - self._t0) * 1000.0
            return {
                "running": self._running,
                "phase": self._phase,
                "done": self._done,
                "total": self._total,
                "detail": self._detail,
                "elapsed_ms": elapsed,
                "history": list(self._history),
            }


PROGRESS = Progress()


def estimate_ms(
    n: int, l: int, modulus_bits: int, *, nodes: int = 0, kind: str = "commit"
) -> float:
    """按实测拟合的代价模型粗估耗时（毫秒），只作为前端「预计」的参考。

    主因是 ``e_[n]`` 的位长 ``E = n·(l+1)``（模幂的指数长度），
    模数按约 ``|N|^1.72`` 放大。实测标定点：

    ====================  =================================  ==========
    配置                   阶段                                 耗时
    ====================  =================================  ==========
    |N|=2048, n=1024, l=128  commit                              27.0 s
    |N|=4096, n=512,  l=128  commit                              49.1 s
    |N|=4096, n=512,  l=128  distribute（8 台）                 378.9 s
    ====================  =================================  ==========

    没有覆盖到的最慢一项是 ``Bootstrap``（RSA 模数生成），
    它的耗时是随机的，不在这里估。
    """
    e_bits = max(n, 1) * (l + 1)
    scale = (max(modulus_bits, 64) / 2048.0) ** 1.72
    commit = 0.206 * e_bits * scale
    if kind == "commit":
        return commit
    return 0.87 * max(nodes, 1) * commit


def _require_session() -> VDSSession:
    if STATE.session is None:
        raise RuntimeError("还没有建立会话，请先调用 /api/setup")
    return STATE.session


def _timed(fn, *args, **kwargs) -> tuple[object, float]:
    t0 = time.perf_counter()
    out = fn(*args, **kwargs)
    return out, (time.perf_counter() - t0) * 1000.0


def _progress_cb(done: int, total: int, detail: str) -> None:
    """传给 ``VDSSession`` 的进度回调。"""
    PROGRESS.tick(done, total, detail)


# ---------------------------------------------------------------------------
# 各步骤
# ---------------------------------------------------------------------------


def op_setup(payload: dict) -> dict:
    n_max = int(payload.get("n_max", 16))
    block_bytes = int(payload.get("block_bytes", 16))
    modulus_bits = int(payload.get("modulus_bits", 512))
    seed = payload.get("seed", "web-demo")

    STATE.reset()
    PROGRESS.clear()
    PROGRESS.begin("① 生成公开参数", 1, f"生成 {modulus_bits} 位隐藏阶群模数（耗时随机）")
    t0 = time.perf_counter()
    session = VDSSession(
        n_max=n_max,
        l=block_bytes * 8,
        lambda_bits=16,
        modulus_bits=modulus_bits,
        seed=str(seed).encode(),
    )
    ms = (time.perf_counter() - t0) * 1000.0
    PROGRESS.tick(1, 1)
    PROGRESS.finish()
    STATE.session = session
    STATE.block_bytes = block_bytes

    return {
        "ok": True,
        "ms": ms,
        "params": {
            "n_max": n_max,
            "block_bytes": block_bytes,
            "l": block_bytes * 8,
            "prime_bits": block_bytes * 8 + 1,
            "N_bits": session.crs.N.bit_length(),
            "g": session.crs.g,
        },
        "message": (
            f"隐藏阶群已生成：|N| = {session.crs.N.bit_length()} 位，"
            f"最多 {n_max} 个块，每块 {block_bytes} 字节。"
        ),
    }


def op_commit(payload: dict) -> dict:
    session = _require_session()

    # 两种内容来源：上传的文件（原始字节，走十六进制）优先；否则用文本框（UTF-8）。
    # 文件走十六进制而不是先解码成文本，是为了二进制安全 —— 图片/压缩包这类
    # 内容按 UTF-8 解码会损坏，而且切块看到的字节数也会变。
    data_hex = payload.get("data_hex")
    if data_hex:
        try:
            data = bytes.fromhex(str(data_hex))
        except ValueError as exc:
            raise ValueError("data_hex 不是合法的十六进制字符串") from exc
        source = str(payload.get("name") or "上传文件")
    else:
        text = payload.get("text", "")
        if not isinstance(text, str):
            raise ValueError("text 必须是字符串")
        data = text.encode("utf-8")
        source = "文本框内容"
    if not data:
        raise ValueError("内容不能为空：请上传一个文件，或在文本框里输入内容")

    PROGRESS.begin("② 切块并承诺", 3, "按块切分")
    (delta, crs_n, values, nbytes), ms = _timed(
        session.commit_bytes, data, STATE.block_bytes, progress=_progress_cb
    )
    STATE.delta, STATE.crs_n, STATE.values = delta, crs_n, values
    STATE.payload = data

    return {
        "ok": True,
        "ms": ms,
        "eta_ms": estimate_ms(
            delta.n, session.l, session.crs.N.bit_length(), kind="commit"
        ),
        "source": source,
        "n": delta.n,
        "nbytes": nbytes,
        "digest": {
            "n": delta.n,
            "U": STATE.num(delta.U),
            "C": STATE.num(delta.C),
        },
        "blocks": [
            {"i": i, "hex": hex(v), "bytes": v.to_bytes(STATE.block_bytes, "big").hex()}
            for i, v in enumerate(values)
        ],
        "message": (
            f"来源 {source}：{nbytes} 字节 → {delta.n} 块；摘要只有 (U, C, n) 三个量，"
            f"U 和 C 各 {delta.U.bit_length()} 位，与文件大小无关。"
        ),
    }


def op_distribute(payload: dict) -> dict:
    session = _require_session()
    if STATE.delta is None:
        raise ValueError("请先调用 /api/commit")

    requested = int(payload.get("nodes", 4))
    n = STATE.delta.n
    # 均分成 k 组；n 不足 k 时按 n 组（空服务器没有意义）
    k = max(1, min(requested, n))
    base = n // k
    extra = n % k
    groups, start = [], 0
    for i in range(k):
        size = base + (1 if i < extra else 0)
        groups.append(list(range(start, start + size)))
        start += size

    PROGRESS.begin("③ 分发到服务器", len(groups), "逐台生成独立证据")
    nodes, ms = _timed(
        session.distribute,
        STATE.delta, STATE.values, groups,
        crs_n=STATE.crs_n,
        progress=_progress_cb,
    )
    STATE.nodes = nodes
    STATE.certs = []
    STATE.pi_K = None
    STATE.attack = "none"

    return {
        "ok": True,
        "ms": ms,
        "requested_nodes": requested,
        "nodes_clamped": requested > n,
        "n": n,
        "eta_ms": estimate_ms(
            STATE.delta.n, session.l, session.crs.N.bit_length(),
            nodes=len(nodes), kind="distribute",
        ),
        "nodes": [
            {
                "id": nd.node_id,
                "indices": list(nd.I),
                "valid": nd.check_local_view(),
                "S": STATE.num(nd.st.S_I),
                "Lambda": STATE.num(nd.st.Lambda_I),
                "bytes": [
                    int(v).to_bytes(STATE.block_bytes, "big").hex() for v in nd.FI
                ],
                "tampered": False,
            }
            for nd in nodes
        ],
        "message": (
            f"文件被分到 {len(nodes)} 台服务器上。每台拿到的证据都是"
            f"一个子向量打开证明（2 个群元素），且都能通过本地视图检查。"
        ),
    }


def _tamper_node(node: StorageNode, index: int) -> StorageNode:
    """让某个节点把某块内容改掉，但**不**更新证据。"""
    pos = node.I.index(index)
    vals = list(node.FI)
    vals[pos] ^= 0xFF
    return StorageNode(
        node.node_id,
        node.session,
        LocalView(
            delta=node.view.delta,
            st=node.st,
            I=node.I,
            FI=tuple(vals),
        ),
    )


def _forge_node(node: StorageNode) -> StorageNode:
    """让某个节点交出一个伪造的 S。"""
    N = node.session.crs.N
    return StorageNode(
        node.node_id,
        node.session,
        LocalView(
            delta=node.view.delta,
            st=Opening(
                S_I=(node.st.S_I * 7919) % N,
                Lambda_I=node.st.Lambda_I,
                I=node.st.I,
            ),
            I=node.I,
            FI=node.FI,
        ),
    )


def op_retrieve(payload: dict) -> dict:
    session = _require_session()
    if not STATE.nodes:
        raise ValueError("请先调用 /api/distribute")

    Q = payload.get("indices")
    if Q is None:
        # 默认：从每台服务器各取一块，保证跨节点
        Q = [nd.I[0] for nd in STATE.nodes if nd.I]
    Q = [int(i) for i in Q]

    nodes, ms = _timed(session.retrieve_from, STATE.nodes, Q)
    F_Q, certs, used = nodes
    STATE.certs = certs

    return {
        "ok": True,
        "ms": ms,
        "Q": Q,
        "F_Q": [hex(v) for v in F_Q],
        "servers": used,
        "certs": [
            {
                "source": c.source,
                "Q": list(c.Q),
                "S": STATE.num(c.pi_Q.S_I),
                "Lambda": STATE.num(c.pi_Q.Lambda_I),
            }
            for c in certs
        ],
        "message": (
            f"向 {len(certs)} 台服务器发起检索，共收到 {len(certs)} 份独立证据；"
            f"每份都是 2 个群元素。"
        ),
    }


def op_aggregate(payload: dict) -> dict:
    session = _require_session()
    if not STATE.certs:
        raise ValueError("请先调用 /api/retrieve")

    client = session.make_client(STATE.delta)
    pi_K, ms = _timed(client.aggregate_certificates, STATE.certs)
    STATE.pi_K = pi_K

    return {
        "ok": True,
        "ms": ms,
        "merged_from": len(STATE.certs),
        "I": list(pi_K.I),
        "S": STATE.num(pi_K.S_I),
        "Lambda": STATE.num(pi_K.Lambda_I),
        "message": (
            f"{len(STATE.certs)} 份证据 → **1** 份；证据大小始终是 2 个群元素，"
            f"不随块数增长。"
        ),
    }


def op_verify(payload: dict) -> dict:
    session = _require_session()
    if STATE.pi_K is None:
        raise ValueError("请先调用 /api/aggregate")

    client = session.make_client(STATE.delta)
    Q = list(STATE.pi_K.I)
    vals = [STATE.values[i] for i in Q]
    report, ms = _timed(client.ver_retrieve, Q, vals, STATE.pi_K)

    return {
        "ok": report.ok,
        "ms": ms,
        "code": report.code.name,
        "code_value": int(report.code),
        "Q": Q,
        "message": report.message,
        "verify_note": (
            "客户端全程只用了自己手里的摘要 delta，"
            "没有向任何服务器索取额外信息。"
        ),
    }


def op_attack(payload: dict) -> dict:
    """制造一次攻击，并报告它在**哪一个环节**被抓住。

    有意思的是：聚合算法本身就有自净能力。
    :func:`svc.agg` 在合并 Λ 之前会用 ``ShamirTrick`` 做**同源自检**
    （``root_x^x == root_y^y``），而两份来自不同数据版本的证据
    **根本不同源**，于是聚合直接失败 —— 连一个可验证的假证明都拼不出来。

    所以本函数给出两条独立的检测路径：

    1. **逐份验证**：对每份凭证单独跑 :func:`svc.verify`，
       指出是哪台服务器、哪一步挂的（``BAD_LAMBDA`` 还是 ``BAD_S_I``）；
    2. **尝试聚合**：报告聚合是否被拒绝。
    """
    session = _require_session()
    if not STATE.nodes:
        raise ValueError("请先调用 /api/distribute")

    kind = payload.get("kind", "tamper")
    which = int(payload.get("node", 0)) % len(STATE.nodes)
    victim = STATE.nodes[which]

    if kind == "tamper":
        index = int(payload.get("index", victim.I[0]))
        evil = _tamper_node(victim, index)
        STATE.attack = f"tamper(node={victim.node_id}, index={index})"
        msg = f"{victim.node_id} 偷偷改了下标 {index} 的内容，但证据没动。"
    elif kind == "forge":
        evil = _forge_node(victim)
        STATE.attack = f"forge(node={victim.node_id})"
        msg = f"{victim.node_id} 交出了一个伪造的证据（S 上随便乘了个数）。"
    else:
        raise ValueError(f"未知攻击类型 {kind!r}")

    replacement = list(STATE.nodes)
    replacement[which] = evil
    STATE.nodes = replacement
    STATE.certs = []
    STATE.pi_K = None

    client = session.make_client(STATE.delta)
    Q = [nd.I[0] for nd in STATE.nodes if nd.I]
    _, certs, _ = session.retrieve_from(STATE.nodes, Q)
    STATE.certs = certs

    # ---- 路径 1：逐份验证 ----
    per_cert = []
    for cert in certs:
        rep = client.ver_retrieve(list(cert.Q), list(cert.F_Q), cert.pi_Q)
        per_cert.append(
            {
                "source": cert.source,
                "Q": list(cert.Q),
                "ok": rep.ok,
                "code": rep.code.name,
                "message": rep.message,
            }
        )

    # ---- 路径 2：尝试聚合 ----
    aggregate_info: dict = {"ok": False, "error": None}
    pi_K = None
    try:
        pi_K = client.aggregate_certificates(certs)
        STATE.pi_K = pi_K
        aggregate_info = {
            "ok": True,
            "I": list(pi_K.I),
            "S": STATE.num(pi_K.S_I),
            "Lambda": STATE.num(pi_K.Lambda_I),
        }
    except Exception as exc:  # noqa: BLE001 - 演示场景，把原因原样带出去
        aggregate_info = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}

    # ---- 聚合若成功，再验证一次 ----
    final = None
    if pi_K is not None:
        I_ = list(pi_K.I)
        rep = client.ver_retrieve(I_, [STATE.values[i] for i in I_], pi_K)
        final = {
            "ok": rep.ok,
            "code": rep.code.name,
            "message": rep.message,
            "Q": I_,
        }

    caught = (not all(c["ok"] for c in per_cert)) or (not aggregate_info["ok"])
    if aggregate_info["ok"] and final is not None:
        caught = caught or (not final["ok"])

    return {
        "ok": True,
        "kind": kind,
        "node": victim.node_id,
        "node_valid": evil.check_local_view(),
        "message": msg,
        "per_cert": per_cert,
        "aggregate": aggregate_info,
        "final": final,
        "caught": caught,
        "verdict": (
            "攻击被抓住" if caught else "⚠ 攻击未被发现（不应发生）"
        ),
    }


def op_full(payload: dict) -> dict:
    """一键跑完整条流水线，返回每一步的结果与耗时。"""
    steps = []

    def run(name: str, fn, arg=None):
        try:
            out = fn(arg or {})
            steps.append({"step": name, **out})
            return out
        except Exception as exc:  # noqa: BLE001
            steps.append(
                {"step": name, "ok": False, "message": f"{type(exc).__name__}: {exc}"}
            )
            return None

    run("setup", op_setup, {k: payload[k] for k in ("n_max", "block_bytes", "modulus_bits")
                            if k in payload})
    run("commit", op_commit, {"text": payload.get("text", "Hello VDS")})
    run("distribute", op_distribute, {"nodes": payload.get("nodes", 4)})
    run("retrieve", op_retrieve, {})
    run("aggregate", op_aggregate, {})
    run("verify", op_verify, {})

    ok = all(s.get("ok") for s in steps)
    return {
        "ok": ok,
        "steps": steps,
        "message": "完整流水线执行完毕。" if ok else "流水线中有步骤失败。",
    }


def op_status(_: dict) -> dict:
    s = STATE
    return {
        "ok": True,
        "ready": s.session is not None,
        "session": (
            None
            if s.session is None
            else {
                "n_max": s.session.n_max,
                "l": s.session.l,
                "N_bits": s.session.crs.N.bit_length(),
                "block_bytes": s.block_bytes,
            }
        ),
        "digest": (
            None
            if s.delta is None
            else {"n": s.delta.n, "U": STATE.num(s.delta.U), "C": STATE.num(s.delta.C)}
        ),
        "nodes": [
            {"id": nd.node_id, "indices": list(nd.I), "valid": nd.check_local_view()}
            for nd in s.nodes
        ],
        "n_certs": len(s.certs),
        "has_merged": s.pi_K is not None,
        "attack": s.attack,
    }


ROUTES = {
    "/api/setup": op_setup,
    "/api/commit": op_commit,
    "/api/distribute": op_distribute,
    "/api/retrieve": op_retrieve,
    "/api/aggregate": op_aggregate,
    "/api/verify": op_verify,
    "/api/attack": op_attack,
    "/api/full": op_full,
    "/api/status": op_status,
}


# ---------------------------------------------------------------------------
# HTTP 层
# ---------------------------------------------------------------------------

_MIME = {
    ".html": "text/html; charset=utf-8",
    ".js": "application/javascript; charset=utf-8",
    ".css": "text/css; charset=utf-8",
    ".svg": "image/svg+xml",
    ".ico": "image/x-icon",
}


class Handler(BaseHTTPRequestHandler):
    server_version = "SVC-VDS-Demo/1.0"

    def log_message(self, fmt, *args):  # noqa: A003
        # 默认实现会往 stderr 打一大堆访问日志，演示时太吵
        return

    # -- 输出辅助 --------------------------------------------------------

    def _send_json(self, obj, status: int = 200) -> None:
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _send_file(self, path: Path) -> None:
        if not path.is_file():
            self._send_json({"ok": False, "error": f"找不到 {path.name}"}, 404)
            return
        body = path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", _MIME.get(path.suffix, "application/octet-stream"))
        self.send_header("Content-Length", str(len(body)))
        # 演示时改完 js/css 刷新就该生效 —— 不加这个浏览器会启发式缓存旧文件
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    # -- 路由 ------------------------------------------------------------

    def do_GET(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path in ("/", "/index.html"):
            self._send_file(WEB_DIR / "index.html")
            return
        if path.startswith("/api/"):
            if path == "/api/status":
                self._send_json(op_status({}))
            elif path == "/api/progress":
                # 故意不取 STATE.lock：长任务霸着它，取了就轮询不到了
                self._send_json({"ok": True, **PROGRESS.snapshot()})
            else:
                self._send_json({"ok": False, "error": "该接口请用 POST"}, 405)
            return
        # 静态资源
        rel = path.lstrip("/")
        candidate = (WEB_DIR / rel).resolve()
        if WEB_DIR.resolve() not in candidate.parents and candidate != WEB_DIR.resolve():
            self._send_json({"ok": False, "error": "路径越界"}, 403)
            return
        self._send_file(candidate)

    def do_POST(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        fn = ROUTES.get(path)
        if fn is None:
            self._send_json({"ok": False, "error": f"未知接口 {path}"}, 404)
            return

        length = int(self.headers.get("Content-Length") or 0)
        raw = self.rfile.read(length) if length else b"{}"
        try:
            payload = json.loads(raw.decode("utf-8")) if raw else {}
        except json.JSONDecodeError as exc:
            self._send_json({"ok": False, "error": f"JSON 解析失败: {exc}"}, 400)
            return

        try:
            with STATE.lock:
                result = fn(payload)
            self._send_json(result)
        except Exception as exc:  # noqa: BLE001
            self._send_json(
                {
                    "ok": False,
                    "error": f"{type(exc).__name__}: {exc}",
                    "traceback": traceback.format_exc(limit=4),
                },
                400,
            )
        finally:
            # 无论成败都收尾，否则前端会看到一个永远「进行中」的阶段
            PROGRESS.finish()


def main() -> None:
    ap = argparse.ArgumentParser(description="SVC/VDS 演示服务器")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8000)
    args = ap.parse_args()

    httpd = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"SVC/VDS 演示服务已启动： http://{args.host}:{args.port}")
    print(f"静态页面目录： {WEB_DIR}")
    print("按 Ctrl+C 停止。")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n已停止。")
    finally:
        httpd.server_close()


if __name__ == "__main__":
    main()
