/* 前端逻辑：只负责调后端 API 并把结果画出来。
 *
 * 密码学运算（承诺、打开、聚合、验证）全部在 Python 后端完成 ——
 * 因为浏览器里没有大整数模幂，而且真把方案搬到前端就等于把
 * 「客户端只持有摘要」这个前提给破坏了。前端的职责是
 * 把每一步的输入输出、耗时、失败原因清楚地展示出来。
 */

const $ = (id) => document.getElementById(id);

const state = {
  digest: null,
  nodes: [],
  certs: [],
  merged: null,
  attack: null,
};

/* ---------------------------------------------------------------- 工具 */

function short(s, keep = 20) {
  if (s == null) return "—";
  s = String(s);
  if (s.length <= keep * 2 + 3) return s;
  return `${s.slice(0, keep)}…${s.slice(-keep)}`;
}

/** HTML 属性转义。完整值虽然只有十六进制字符，转义一下更稳妥。 */
function escapeAttr(s) {
  return String(s)
    .replace(/&/g, "&amp;")
    .replace(/"/g, "&quot;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

/** 展开/收起一个值，并同步它所在的块（块的 white-space 要跟着变）。 */
function setExpanded(el, open) {
  el.classList.toggle("open", open);
  const blk = el.closest(".blk");
  if (blk) blk.classList.toggle("open", open);
}

/** 大整数的可展开显示：默认「指纹 + 位长」，点击后展开**完整**十六进制。
 *
 * 512 位的群元素展开后是 130 个字符（0x + 128 位），靠 CSS 的
 * word-break 自动折行。完整值同时放进隐藏的 .hx-f 与 data-copy：
 * 前者供人眼阅读/选中，后者供 ⧉ 按钮复制。
 */
function hexCell(n) {
  if (n == null) return '<span class="na">—</span>';
  const full = n.hex || "";
  return (
    `<span class="hx" role="button" tabindex="0" ` +
      `title="点击展开完整值（${n.bits} 位）">` +
      `<span class="hx-c">${n.fp}<em>${n.bits}b</em></span>` +
      `<span class="hx-f">${escapeAttr(full)}</span>` +
    `</span>` +
    `<span class="cp" role="button" tabindex="0" title="复制完整值" ` +
      `data-copy="${escapeAttr(full)}">⧉</span>`
  );
}

/** 内容字节块：同样是「截断显示 + 点击展开完整字节」。 */
function bytesCell(hexStr) {
  if (!hexStr) return '<span class="na">—</span>';
  return (
    `<span class="hx" role="button" tabindex="0" title="点击展开完整字节">` +
      `<span class="hx-c">${short(hexStr, 10)}</span>` +
      `<span class="hx-f">${escapeAttr(hexStr)}</span>` +
    `</span>`
  );
}

/** 复制到剪贴板。localhost 下 navigator.clipboard 可用，另有 execCommand 兜底。 */
async function copyText(text, el) {
  if (!text) return;
  try {
    if (navigator.clipboard && window.isSecureContext) {
      await navigator.clipboard.writeText(text);
    } else {
      const ta = document.createElement("textarea");
      ta.value = text;
      ta.style.position = "fixed";
      ta.style.opacity = "0";
      document.body.appendChild(ta);
      ta.select();
      document.execCommand("copy");
      ta.remove();
    }
    if (el) {
      el.textContent = "✓";
      el.classList.add("done");
      setTimeout(() => {
        el.textContent = "⧉";
        el.classList.remove("done");
      }, 1200);
    }
  } catch (err) {
    log(`复制失败：${err.message}`, "err");
  }
}

function nowStamp() {
  const d = new Date();
  return d.toTimeString().slice(0, 8);
}

function log(message, cls = "", ms = null) {
  const box = $("log");
  const line = document.createElement("div");
  line.className = `line ${cls}`;
  line.innerHTML =
    `<span class="t">${nowStamp()}</span>` +
    `<span class="m"></span>` +
    (ms == null ? "" : `<span class="ms">${ms.toFixed(1)} ms</span>`);
  line.querySelector(".m").textContent = message;
  box.appendChild(line);
  box.scrollTop = box.scrollHeight;
}

function logHead(title) {
  const box = $("log");
  const line = document.createElement("div");
  line.className = "line head";
  line.innerHTML = `<span class="t"></span><span class="m"></span>`;
  line.querySelector(".m").textContent = `── ${title} ──`;
  box.appendChild(line);
  box.scrollTop = box.scrollHeight;
}

async function post(path, body = {}) {
  const res = await fetch(path, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
  const data = await res.json().catch(() => ({ ok: false, error: "响应不是 JSON" }));
  if (!res.ok || data.ok === false) {
    throw new Error(data.error || `HTTP ${res.status}`);
  }
  return data;
}

/* ------------------------------------------------------------ 渲染函数 */

function renderDigest(d) {
  state.digest = d;
  $("panel-digest").hidden = false;
  $("d-n").textContent = d.n;
  $("d-U").innerHTML = hexCell(d.U);
  $("d-C").innerHTML = hexCell(d.C);
}

function renderNodes(nodes) {
  state.nodes = nodes;
  $("panel-nodes").hidden = false;
  const box = $("nodes");
  box.innerHTML = "";

  for (const nd of nodes) {
    const el = document.createElement("div");
    el.className = "node" + (nd.valid ? "" : " bad");
    el.innerHTML = `
      <h4>${nd.id}<span class="tag">${nd.valid ? "本地视图合法" : "视图不合法"}</span></h4>
      <dl>
        <dt>持有下标</dt><dd>${nd.indices.join(", ") || "（空）"}</dd>
        <dt>S<sub>I</sub></dt><dd>${hexCell(nd.S)}</dd>
        <dt>Λ<sub>I</sub></dt><dd>${hexCell(nd.Lambda)}</dd>
      </dl>
      <div class="blocks"></div>`;
    const blocks = el.querySelector(".blocks");
    nd.indices.forEach((idx, k) => {
      const b = document.createElement("span");
      b.className = "blk";
      b.innerHTML = `<em>#${idx}</em>`;
      b.insertAdjacentHTML("beforeend", bytesCell(nd.bytes[k]));
      blocks.appendChild(b);
    });
    box.appendChild(el);
  }
}

function renderCerts(data) {
  state.certs = data.certs;
  $("panel-flow").hidden = false;

  const box = $("certs-list");
  box.innerHTML = "";
  for (const c of data.certs) {
    box.insertAdjacentHTML(
      "beforeend",
      `<div class="row"><span>${c.source} · [${c.Q.join(",")}]</span>
       <span class="val">
         <i class="lab">S</i>${hexCell(c.S)}<br>
         <i class="lab">Λ</i>${hexCell(c.Lambda)}
       </span></div>`
    );
  }
  box.insertAdjacentHTML(
    "beforeend",
    `<div class="row"><span>共收到</span><span>${data.certs.length} 份证据</span></div>`
  );
}

function renderMerged(m) {
  state.merged = m;
  const box = $("merged-body");
  box.innerHTML = `
    <div class="row"><span>来源</span><span>${m.merged_from} 份 → 1 份</span></div>
    <div class="row"><span>覆盖下标</span><span>[${m.I.join(",")}]</span></div>
    <div class="row"><span>S<sub>I</sub></span><span class="val">${hexCell(m.S)}</span></div>
    <div class="row"><span>Λ<sub>I</sub></span><span class="val">${hexCell(m.Lambda)}</span></div>`;
}

function renderVerify(v) {
  $("panel-flow").hidden = false;
  const box = $("verify-body");
  const ok = v.ok;
  box.innerHTML = `
    <div class="verdict ${ok ? "ok" : "bad"}">
      ${ok ? "✓ 验证通过" : "✗ 验证失败"}
      <small>${v.code} · ${v.ms.toFixed(1)} ms</small>
    </div>
    <div class="row"><span>校验块数</span><span>${v.Q.length}</span></div>
    <div class="row"><span>说明</span><span>${ok ? "全部内容完整" : v.message}</span></div>
    <div style="margin-top:8px;color:var(--dim);font-size:11.5px">${v.verify_note || ""}</div>`;
}

async function refreshNodes() {
  const st = await post("/api/status");
  if (st.nodes && st.nodes.length) {
    // status 只给精简信息，完整信息要靠 distribute 的返回，这里只更新合法性
    const box = $("nodes");
    [...box.children].forEach((el, i) => {
      const nd = st.nodes[i];
      if (!nd) return;
      const good = nd.valid;
      el.classList.toggle("bad", !good);
      const tag = el.querySelector(".tag");
      tag.textContent = good ? "本地视图合法" : "视图不合法";
    });
  }
  return st;
}

/* ------------------------------------------------------------ 各步动作 */

async function doSetup() {
  logHead("① Bootstrap —— 生成公开参数");
  const r = await post("/api/setup", {
    n_max: +$("n_max").value,
    block_bytes: +$("block_bytes").value,
    modulus_bits: +$("modulus_bits").value,
    seed: "web-demo",
  });
  log(
    `|N| = ${r.params.N_bits} 位，g = ${r.params.g}，n_max = ${r.params.n_max}，` +
    `每块 ${r.params.block_bytes} 字节（l = ${r.params.l} 位，素数 ${r.params.prime_bits} 位）`,
    "ok", r.ms
  );
}

async function doCommit() {
  logHead("② 切块并承诺");
  const r = await post("/api/commit", { text: $("text").value });
  renderDigest(r.digest);
  log(`${r.nbytes} 字节 → ${r.n} 块`, "ok", r.ms);
  log(`U = ${r.digest.U.fp} (${r.digest.U.bits} 位)，C = ${r.digest.C.fp} (${r.digest.C.bits} 位) —— 摘要与文件大小无关`);
}

async function doDistribute() {
  logHead("③ 分发到服务器");
  const r = await post("/api/distribute", { nodes: +$("n_nodes").value });
  renderNodes(r.nodes);
  log(`${r.nodes.length} 台服务器各自拿到一块子集与一个证据`, "ok", r.ms);
  for (const nd of r.nodes) {
    log(`  ${nd.id} 持有 [${nd.indices.join(",")}]  本地视图 ${nd.valid ? "合法" : "不合法"}`);
  }
}

async function doRetrieve() {
  logHead("④ 跨服务器检索");
  const r = await post("/api/retrieve", {});
  renderCerts(r);
  log(`请求下标 [${r.Q.join(",")}]，落在 ${r.servers.length} 台服务器上`, "ok", r.ms);
  for (const c of r.certs) {
    log(`  ${c.source} 返回 [${c.Q.join(",")}]，证据 2 个群元素`);
  }
}

async function doAggregate() {
  logHead("⑤ 聚合多份证据成一个");
  const r = await post("/api/aggregate", {});
  renderMerged(r);
  log(`${r.merged_from} 份证据 → 1 份，覆盖 [${r.I.join(",")}]`, "ok", r.ms);
}

async function doVerify() {
  logHead("⑥ 客户端验证");
  const r = await post("/api/verify", {});
  renderVerify(r);
  log(r.ok ? `验证通过：${r.Q.length} 块内容全部完整` : `验证失败：${r.code} —— ${r.message}`,
      r.ok ? "ok" : "bad", r.ms);
}

async function doAttack(kind) {
  logHead(kind === "tamper" ? "☠ 攻击：服务器篡改内容" : "☠ 攻击：服务器伪造证据");
  const a = await post("/api/attack", { kind, node: 0 });
  log(a.message, "bad");
  log(`  ${a.node} 的本地视图检查：${a.node_valid ? "通过" : "已失败"}`);
  await refreshNodes();

  // 路径 1：逐份凭证单独验证
  log("路径 1 —— 对每份凭证单独验证：");
  for (const c of a.per_cert) {
    log(`  ${c.source} [${c.Q.join(",")}] → ${c.ok ? "通过" : `失败（${c.code}）`}`,
        c.ok ? "ok" : "bad");
  }

  // 路径 2：尝试聚合
  log("路径 2 —— 尝试把多份证据聚合成一个：");
  if (a.aggregate.ok) {
    log(`  聚合成功，覆盖 [${a.aggregate.I.join(",")}]`, "ok");
    renderMerged({ merged_from: a.per_cert.length, ...a.aggregate });
  } else {
    log(`  聚合被拒绝：${a.aggregate.error}`, "bad");
    log("  （聚合算法自带同源自检，两份来自不同数据版本的证据根本拼不到一起）");
  }

  if (a.final) {
    renderVerify({
      ok: a.final.ok, code: a.final.code, message: a.final.message,
      Q: a.final.Q, ms: 0, verify_note: "聚合后仍按正常流程验证一次。",
    });
    log(`  聚合后再验证：${a.final.ok ? "通过" : `失败（${a.final.code}）`}`,
        a.final.ok ? "bad" : "ok");
  }

  log(a.verdict, a.caught ? "ok" : "bad");
}


async function doFull() {
  logHead("一键跑完整流程");
  $("log").innerHTML = "";
  await doSetup();
  await doCommit();
  await doDistribute();
  await doRetrieve();
  await doAggregate();
  await doVerify();
  logHead("完成");
  log("摘要始终 3 个量；证据始终 2 个群元素；验证时间不随块数增长。");
}

async function doReset() {
  state.nodes = [];
  state.certs = [];
  state.merged = null;
  $("log").innerHTML = "";
  for (const id of ["panel-digest", "panel-nodes", "panel-flow"]) $(id).hidden = true;
  $("nodes").innerHTML = "";
  $("certs-list").innerHTML = "—";
  $("merged-body").innerHTML = "—";
  $("verify-body").innerHTML = "—";
  $("btn-expand").textContent = "⤢ 展开全部完整值";
  log("已重置界面；后端的会话会在下一次「建立会话」时重建。");
}

/* ------------------------------------------------------------ 事件绑定 */

function bind(id, fn, label) {
  $(id).addEventListener("click", async () => {
    const btn = $(id);
    btn.disabled = true;
    try {
      await fn();
    } catch (err) {
      log(`${label} 失败：${err.message}`, "err");
    } finally {
      btn.disabled = false;
    }
  });
}

bind("btn-setup", doSetup, "建立会话");
bind("btn-commit", doCommit, "切块并承诺");
bind("btn-distribute", doDistribute, "分发");
bind("btn-retrieve", doRetrieve, "检索");
bind("btn-aggregate", doAggregate, "聚合");
bind("btn-verify", doVerify, "验证");
bind("btn-tamper", () => doAttack("tamper"), "篡改攻击");
bind("btn-forge", () => doAttack("forge"), "伪造攻击");
bind("btn-full", doFull, "一键演示");
bind("btn-reset", doReset, "重置");

/* ---- 完整值：点击展开 / 回车展开 / ⧉ 复制 ----
 *
 * 用事件委托挂在 document 上，这样每次重新渲染（innerHTML 整个换掉）
 * 都不需要重新绑定。
 */
document.addEventListener("click", (e) => {
  if (!(e.target instanceof Element)) return;
  const cp = e.target.closest(".cp");
  if (cp) {
    copyText(cp.dataset.copy || "", cp);
    return;
  }
  const hx = e.target.closest(".hx");
  if (hx) setExpanded(hx, !hx.classList.contains("open"));
});

document.addEventListener("keydown", (e) => {
  if (e.key !== "Enter" && e.key !== " ") return;
  if (!(e.target instanceof Element)) return;
  const el = e.target.closest(".hx, .cp");
  if (!el) return;
  e.preventDefault();
  if (el.classList.contains("cp")) copyText(el.dataset.copy || "", el);
  else setExpanded(el, !el.classList.contains("open"));
});

$("btn-expand").addEventListener("click", () => {
  const anyClosed = !!document.querySelector(".hx:not(.open)");
  document.querySelectorAll(".hx").forEach((el) => setExpanded(el, anyClosed));
  $("btn-expand").textContent = anyClosed ? "⤡ 收起全部" : "⤢ 展开全部完整值";
});

log("就绪。点「一键跑完整流程」开始，或按 ①②③④⑤⑥ 分步观察。");
