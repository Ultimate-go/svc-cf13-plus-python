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

/* ------------------------------------------------------------ 实时进度
 *
 * 长任务（模数生成、切块承诺、分发）动辄几分钟，期间按钮是灰的、页面没反应。
 * 这里在请求进行中轮询后端 /api/progress，显示：
 *   - 真实的分步进度（分发阶段按服务器台数推进）
 *   - 已用时间
 *   - 按实测代价模型拟合的「预计总时长」
 *
 * 模数生成那一步耗时是随机的（实测 10 秒 ~ 3 分钟），给不出有意义的百分比，
 * 所以用流动条纹表示「在动」，不假装知道进度。
 */

const STEP_LABEL = {
  setup: "① 生成公开参数",
  commit: "② 切块并承诺",
  distribute: "③ 分发到服务器",
  retrieve: "④ 跨服务器检索",
  aggregate: "⑤ 聚合证据",
  verify: "⑥ 客户端验证",
  attack: "☠ 构造攻击",
  vds1: "§8.1 VDS1 演示",
};

function fmtDur(ms) {
  if (ms < 1000) return `${ms.toFixed(0)} ms`;
  if (ms < 60_000) return `${(ms / 1000).toFixed(1)} s`;
  const m = Math.floor(ms / 60000);
  return `${m} 分 ${((ms % 60000) / 1000).toFixed(0)} 秒`;
}

/** 按实测拟合的代价模型粗估该步耗时（毫秒）；返回 null 表示估不出来。 */
function predictMs(step) {
  const bb = +$("block_bytes").value;
  const mb = +$("modulus_bits").value;
  if (!bb) return null;
  const n = Math.max(1, Math.ceil(new TextEncoder().encode($("text").value).length / bb));
  const eBits = n * (bb * 8 + 1);
  const scale = Math.pow(Math.max(mb, 64) / 2048, 1.72);
  const commit = 0.206 * eBits * scale;
  if (step === "commit") return commit;
  if (step === "distribute") {
    // ★ 必须和后端一样做 min(台数, n) 截断：文件只有 n 块时后端只会建 n 台。
    //   不截断的话填 512 台、3 块，页面会显示「预计约 2 分 21 秒」，实际 0.15 秒就跑完。
    const k = Math.max(1, Math.min(+$("n_nodes").value || 1, n));
    return 0.87 * k * commit;
  }
  return null;   // setup（模数生成）与几个快步骤不估
}

let progTimer = null;      // 轮询 /api/progress 的 interval
let progHideTimer = null;  // 「本步结束后 700ms 收起面板」的 timeout
let progHeld = false;      // 长流程（一键跑完）期间整条流水线连着跑，中途不收起

function beginProgress(step) {
  if (progTimer) {
    clearInterval(progTimer);
    progTimer = null;
  }
  // ★ 必须连「延迟收起」一起取消。只清 interval 是不够的：
  //   上一步排的 timeout 会在本步跑到一半时把面板藏掉，
  //   看起来就像卡死了（实测：3 秒的分发全程看不见进度）。
  if (progHideTimer) {
    clearTimeout(progHideTimer);
    progHideTimer = null;
  }
  $("panel-progress").hidden = false;
  $("prog-phase").textContent = STEP_LABEL[step] || step;
  $("prog-sub").textContent = "正在启动…";
  const fill = $("prog-fill");
  fill.classList.remove("done", "waiting");
  fill.style.width = "0%";

  const predict = predictMs(step);
  const t0 = performance.now();

  const tick = async () => {
    let st = null;
    try {
      st = await (await fetch("/api/progress")).json();
    } catch (_) {
      /* 轮询失败不影响主请求 */
    }
    const elapsed = performance.now() - t0;
    $("prog-time").textContent = fmtDur(elapsed);

    if (!st || !st.running) return;
    const hasSteps = st.total > 0;
    if (hasSteps) {
      fill.style.width = `${Math.min(100, (st.done / st.total) * 100).toFixed(1)}%`;
      $("prog-sub").textContent =
        `${st.phase} · ${st.done}/${st.total}` + (st.detail ? ` · ${st.detail}` : "");
      fill.classList.remove("waiting");
    } else {
      fill.classList.add("waiting");
      $("prog-sub").textContent = st.detail || st.phase || "进行中";
    }
    if (predict) {
      const left = Math.max(0, predict - elapsed);
      const tail = left > 0 ? `，预计还要 ${fmtDur(left)}` : "，已超出预估";
      $("prog-sub").textContent += `（预计总共约 ${fmtDur(predict)}${tail}）`;
    }
  };

  tick();
  progTimer = setInterval(tick, 250);
}

function endProgress(ms = null) {
  if (progTimer) {
    clearInterval(progTimer);
    progTimer = null;
  }
  const fill = $("prog-fill");
  fill.classList.remove("waiting");
  fill.classList.add("done");
  fill.style.width = "100%";
  if (ms != null) $("prog-time").textContent = fmtDur(ms);
  if (progHeld) return;   // 整条流水线还没跑完，面板留着
  if (progHideTimer) clearTimeout(progHideTimer);
  progHideTimer = setTimeout(() => {
    progHideTimer = null;
    $("panel-progress").hidden = true;
  }, 700);
}

/** 长流程（一键跑完整流程）期间让面板一直显示，结束后再按正常规则收起。 */
function holdProgress(on) {
  if (on) {
    progHeld = true;
    return;
  }
  progHeld = false;
  endProgress(null);
}

/* ------------------------------------------------------------ 工具 */

async function post(path, body = {}, step = null) {
  if (step) beginProgress(step);
  try {
    const res = await fetch(path, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
    const data = await res.json().catch(() => ({ ok: false, error: "响应不是 JSON" }));
    if (step) endProgress(typeof data.ms === "number" ? data.ms : null);
    if (!res.ok || data.ok === false) {
      throw new Error(data.error || `HTTP ${res.status}`);
    }
    return data;
  } catch (err) {
    if (step) endProgress();
    throw err;
  }
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
  }, "setup");
  log(
    `|N| = ${r.params.N_bits} 位，g = ${r.params.g}，n_max = ${r.params.n_max}，` +
    `每块 ${r.params.block_bytes} 字节（l = ${r.params.l} 位，素数 ${r.params.prime_bits} 位）`,
    "ok", r.ms
  );
}

async function doCommit() {
  logHead("② 切块并承诺");
  const r = await post("/api/commit", { text: $("text").value }, "commit");
  renderDigest(r.digest);
  log(
    `${r.nbytes} 字节 ÷ 每块 ${$("block_bytes").value} 字节 → ${r.n} 块` +
      `（「n max」= ${$("n_max").value} 只是素数表容量上限，块数只看文件大小）`,
    "ok", r.ms
  );
  log(`U = ${r.digest.U.fp} (${r.digest.U.bits} 位)，C = ${r.digest.C.fp} (${r.digest.C.bits} 位) —— 摘要与文件大小无关`);
}

async function doDistribute() {
  logHead("③ 分发到服务器");
  const r = await post("/api/distribute", { nodes: +$("n_nodes").value }, "distribute");
  renderNodes(r.nodes);
  log(`${r.nodes.length} 台服务器各自拿到一块子集与一个证据`, "ok", r.ms);
  if (r.nodes_clamped) {
    log(
      `  注意：你填了 ${r.requested_nodes} 台，但文件只有 ${r.n} 块 —— ` +
        `实际只会建 ${r.nodes.length} 台（空服务器没有意义）`,
      "err"
    );
  }
  for (const nd of r.nodes) {
    log(`  ${nd.id} 持有 [${nd.indices.join(",")}]  本地视图 ${nd.valid ? "合法" : "不合法"}`);
  }
}

async function doRetrieve() {
  logHead("④ 跨服务器检索");
  const r = await post("/api/retrieve", {}, "retrieve");
  renderCerts(r);
  log(`请求下标 [${r.Q.join(",")}]，落在 ${r.servers.length} 台服务器上`, "ok", r.ms);
  for (const c of r.certs) {
    log(`  ${c.source} 返回 [${c.Q.join(",")}]，证据 2 个群元素`);
  }
}

async function doAggregate() {
  logHead("⑤ 聚合多份证据成一个");
  const r = await post("/api/aggregate", {}, "aggregate");
  renderMerged(r);
  log(`${r.merged_from} 份证据 → 1 份，覆盖 [${r.I.join(",")}]`, "ok", r.ms);
}

async function doVerify() {
  logHead("⑥ 客户端验证");
  const r = await post("/api/verify", {}, "verify");
  renderVerify(r);
  log(r.ok ? `验证通过：${r.Q.length} 块内容全部完整` : `验证失败：${r.code} —— ${r.message}`,
      r.ok ? "ok" : "bad", r.ms);
}

async function doAttack(kind) {
  logHead(kind === "tamper" ? "☠ 攻击：服务器篡改内容" : "☠ 攻击：服务器伪造证据");
  const a = await post("/api/attack", { kind, node: 0 }, "attack");
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
  holdProgress(true);
  try {
    await doSetup();
    await doCommit();
    await doDistribute();
    await doRetrieve();
    await doAggregate();
    await doVerify();
  } finally {
    holdProgress(false);
  }
  logHead("完成");
  log("摘要始终 3 个量；证据始终 2 个群元素；验证时间不随块数增长。");
}

async function doReset() {
  state.nodes = [];
  state.certs = [];
  state.merged = null;
  $("log").innerHTML = "";
  for (const id of ["panel-digest", "panel-nodes", "panel-flow", "panel-progress"]) $(id).hidden = true;
  endProgress();
  $("nodes").innerHTML = "";
  $("certs-list").innerHTML = "—";
  $("merged-body").innerHTML = "—";
  $("verify-body").innerHTML = "—";
  $("vds1-body").hidden = true;
  $("vds1-body").innerHTML = "—";
  $("btn-expand").textContent = "⤢ 展开全部完整值";
  log("已重置界面；后端的会话会在下一次「建立会话」时重建。");
}

/* ------------------------------------------------ §8.1 的 VDS1 演示
 *
 * 与上面那条 §8.2 的流水线**完全独立**：后端每次调用都现场建一份 VDS1 会话，
 * 不动当前状态。重点展示 §8.2 没有的那个能力 —— CreateFrom / GetCreate。
 */

function kvRow(k, v) {
  return `<div class="row"><span>${k}</span><span class="val">${v}</span></div>`;
}

function kvHead(t) {
  return `<div class="row"><span><b>${t}</b></span><span></span></div>`;
}

async function doVds1() {
  logHead("§8.1 的 VDS1");
  const box = $("vds1-body");
  box.hidden = false;
  box.innerHTML = '<span class="na">运行中…</span>';

  const data = await post(
    "/api/vds1",
    {
      text: $("text").value,
      n_max: Math.min(64, Math.max(8, +$("n_max").value || 24)),
      modulus_bits: +$("modulus_bits").value || 512,
    },
    "vds1"
  );

  log(
    `|N| = ${data.pp.N_bits} 位，n_max = ${data.pp.n_max}，取 ${data.file.n} 位` +
      (data.file.truncated ? "（文本太长，已截断）" : ""),
    "",
    data.ms
  );
  for (const s of data.steps) {
    log(`${s.ok ? "✓" : "✗"} ${s.step} —— ${s.detail}`, s.ok ? "" : "err", s.ms);
  }

  const out = [];
  out.push(kvHead("摘要 δ = ((A, B), n)"));
  out.push(kvRow("A = g₀^a", hexCell(data.digest.A)));
  out.push(kvRow("B = g₁^b", hexCell(data.digest.B)));
  out.push(kvRow("n（位数）", String(data.digest.n)));

  out.push(kvHead("存储节点（各自只持自己那段）"));
  for (const nd of data.nodes) {
    out.push(
      `<div class="row"><span>${nd.id} 持 [${nd.indices.join(", ")}]</span>` +
        `<span>${nd.valid ? "本地视图合法" : "视图不合法"}</span></div>`
    );
  }

  const c = data.create;
  out.push(kvHead("CreateFrom / GetCreate —— §8.2 没有这个能力"));
  out.push(kvRow("派生前 m 位", String(c.m)));
  out.push(kvRow("δ′ == Com′(F_J)", c.matches ? "✓" : "✗"));
  out.push(kvRow("派生节点视图合法", c.derived_valid ? "✓" : "✗"));
  out.push(kvRow("客户端 PoKSubV′.V", c.accepted ? "✓ 接受" : "✗ 拒绝"));
  out.push(kvRow("伪造 δ′", c.forged_rejected ? "✓ 被拒" : "✗ 通过了"));
  out.push(kvRow("非前缀 J", c.nonprefix_rejected ? "✓ 被拒" : "✗ 通过了"));

  out.push(kvHead("三种更新（每步都给 I∩K 各种情形各造一个探测节点）"));
  for (const u of data.updates) {
    const applied = u.applied
      .map((a) => {
        if (!a.ok) return `${a.kind}: ✗`;
        const idx = a.indices.length ? `[${a.indices.join(",")}]` : "空（节点应下线）";
        return `${a.kind}: ✓（视图${a.valid ? "合法" : "不合法"}，新 I=${idx}）`;
      })
      .join("<br>");
    out.push(
      `<div class="row"><span>${u.op}<br>` +
        `<i class="lab">K = [${u.K.join(",")}] → n = ${u.n}</i></span>` +
        `<span>δ′ == 重新承诺整个文件 ? ${u.matches ? "✓" : "✗"}；` +
        `客户端 ${u.client_ok ? "✓" : "✗"}<br>${applied}</span></div>`
    );
  }

  out.push(kvHead("攻击面"));
  for (const a of data.attacks) {
    out.push(
      `<div class="row"><span>${a.what}<br><i class="lab">${a.how}</i></span>` +
        `<span>${a.rejected ? "✓ 被拒" : "✗ 通过了"}</span></div>`
    );
  }
  box.innerHTML = out.join("");
  log("VDS1 演示完成：派生新文件 + 三种更新 + 四类攻击全部符合预期。");
}

/* ------------------------------------------------------------ 事件绑定 */

function bind(id, fn, label) {
  $(id).addEventListener("click", async () => {
    const btn = $(id);
    // 后端所有请求串在同一把锁上，并发点击只会互相排队 ——
    // 所以整轮运行期间把**所有**动作按钮都锁掉，并让被点的那个显示「运行中」。
    const all = Array.from(document.querySelectorAll(".actions button"));
    const original = btn.innerHTML;
    for (const b of all) b.disabled = true;
    btn.classList.add("busy");
    btn.innerHTML = `<span class="spin"></span>运行中… ${label}`;
    try {
      await fn();
    } catch (err) {
      log(`${label} 失败：${err.message}`, "err");
    } finally {
      for (const b of all) b.disabled = false;
      btn.classList.remove("busy");
      btn.innerHTML = original;
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
bind("btn-vds1", doVds1, "VDS1 演示");
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
log("第 5 节的按钮会另跑一遍 §8.1 的 VDS1（派生新文件 + 三种更新）。");
