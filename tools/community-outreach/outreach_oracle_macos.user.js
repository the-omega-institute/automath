// ==UserScript==
// @name         Outreach Oracle Bridge (macOS, multi-turn)
// @namespace    omega-outreach
// @version      1.2
// @description  Outreach-pipeline ChatGPT bridge with multi-turn follow-up support. Talks to outreach_oracle_server.py on :8766. Distinct from the paper-pipeline oracle (which is single-shot on :8765).
// @match        https://chatgpt.com/*
// @match        https://chat.openai.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @connect      localhost
// @connect      127.0.0.1
// @run-at       document-idle
// ==/UserScript==

// FORKED FROM: tools/chatgpt-oracle/chatgpt_oracle_macos.user.js v4.10
// Differences (search "OUTREACH ADD" / "OUTREACH CHANGE" comments):
//   - SERVER port 8766 (paper oracle is 8765, run side by side)
//   - All GM_setValue keys namespaced under "outreach_*" (no clash)
//   - URL flag is ?outreach=N (paper uses ?oracle=N)
//   - Panel branding distinct (purple/cyan, "[outreach]" prefix)
//   - Task payload may carry conversation_url + is_followup → navigate to
//     the existing ChatGPT chat URL first, then post follow-up there
//   - After response, captures window.location.href and POSTs as chatgpt_url
//     so the server pins the conversation_id ↔ chat URL for future turns

(function () {
  "use strict";

  // OUTREACH CHANGE
  const SERVER = "http://localhost:8766";
  const POLL_INTERVAL = 30000;
  const STABLE_CHECKS = 3;
  const STABLE_INTERVAL = 60000;
  const MAX_WAIT = 7200000;
  const SCRIPT_VERSION = "outreach-1.2";

  let busy = false;
  // OUTREACH CHANGE: per-tab active flag via sessionStorage (NOT GM_setValue,
  // which is cross-tab and caused new ChatGPT windows the user opens for
  // personal use to inherit ACTIVE state and start stealing tasks).
  // Each tab now opts in independently by clicking the dashboard toggle.
  let active = (() => {
    try { return sessionStorage.getItem("outreach_active") === "1"; }
    catch { return false; }
  })();

  // ── Logging ──────────────────────────────────────────────────────────
  const logHistory = [];
  function log(msg) {
    const ts = new Date().toLocaleTimeString();
    const entry = `${ts} ${msg}`;
    console.log(`[outreach] ${entry}`);
    logHistory.push(entry);
    if (logHistory.length > 20) logHistory.shift();
    updatePanel();
  }

  function toggleActive() {
    active = !active;
    try { sessionStorage.setItem("outreach_active", active ? "1" : "0"); } catch {}
    log(active ? "ACTIVATED — polling will start (this tab only)" : "PAUSED — your ChatGPT is free");
    updatePanel();
  }

  // ── Status panel (OUTREACH CHANGE: distinct color/branding) ──────────
  let panel = null;
  function ensurePanel() {
    if (panel && document.body.contains(panel)) return;
    panel = document.createElement("div");
    panel.id = "outreach-oracle-panel";
    panel.style.cssText = `
      position: fixed; bottom: 12px; right: 12px; z-index: 99999;
      background: #1d1d3a; color: #9af; font-family: monospace; font-size: 11px;
      padding: 8px 12px; border-radius: 6px; max-width: 460px; max-height: 320px;
      overflow-y: auto; box-shadow: 0 2px 12px rgba(80,40,180,0.5); opacity: 0.93;
      line-height: 1.4; border: 1px solid #5577cc;
    `;
    document.body.appendChild(panel);
  }

  function updatePanel() {
    ensurePanel();
    const statusColor = active ? (busy ? "#ff0" : "#9af") : "#f55";
    const statusText = active ? (busy ? "BUSY" : "ACTIVE") : "PAUSED";
    const btnText = active ? "⏸ Pause" : "▶ Start";
    const btnColor = active ? "#f55" : "#9af";
    const lines = logHistory.slice(-10).map(l => `<div>${l}</div>`).join("");
    panel.innerHTML = `
      <div style="display:flex;justify-content:space-between;align-items:center;gap:8px">
        <b style="color:#cdf">[Outreach Oracle ${SCRIPT_VERSION}]</b>
        <span style="color:${statusColor};font-weight:bold">${statusText}</span>
        <button id="outreach-toggle" style="background:${btnColor};color:#000;border:none;border-radius:3px;padding:2px 8px;cursor:pointer;font-size:11px;font-weight:bold">${btnText}</button>
      </div>
      <hr style="border-color:#446;margin:4px 0">
      ${lines}`;
    const btn = document.getElementById("outreach-toggle");
    if (btn) btn.addEventListener("click", toggleActive);
  }

  // ── HTTP helpers ─────────────────────────────────────────────────────
  function serverGet(path) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: "GET",
        url: `${SERVER}${path}`,
        timeout: 10000,
        onload: (r) => {
          try { resolve(JSON.parse(r.responseText)); }
          catch (e) { reject(e); }
        },
        onerror: () => reject(new Error("network error")),
        ontimeout: () => reject(new Error("timeout")),
      });
    });
  }

  function serverPost(path, data) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: "POST",
        url: `${SERVER}${path}`,
        headers: { "Content-Type": "application/json" },
        data: JSON.stringify(data),
        timeout: 30000,
        onload: (r) => {
          try { resolve(JSON.parse(r.responseText)); }
          catch (e) { reject(e); }
        },
        onerror: () => reject(new Error("network error")),
        ontimeout: () => reject(new Error("timeout")),
      });
    });
  }

  function sleep(ms) {
    return new Promise((r) => setTimeout(r, ms));
  }

  // ── Persistent task state (survives page navigation) ─────────────────
  // OUTREACH CHANGE: keys namespaced under outreach_*
  // OUTREACH ADD: in_flight_task_id tracks the currently-being-processed
  // task across full page reloads (ChatGPT 5.5 does full reload on first
  // /c/<uuid> redirect, dropping in-memory busy state). With in_flight set,
  // a re-entry of processTask while on the original /c/<uuid> page resumes
  // waitForResponse() instead of re-navigating + re-entering the prompt.
  function saveTaskState(task) {
    GM_setValue("outreach_current_task", JSON.stringify(task));
    GM_setValue("outreach_task_phase", "pending");
  }
  function loadTaskState() {
    try {
      const s = GM_getValue("outreach_current_task", "");
      return s ? JSON.parse(s) : null;
    } catch { return null; }
  }
  function getTaskPhase() {
    return GM_getValue("outreach_task_phase", "");
  }
  function setTaskPhase(phase) {
    GM_setValue("outreach_task_phase", phase);
  }
  function clearTaskState() {
    GM_setValue("outreach_current_task", "");
    GM_setValue("outreach_task_phase", "");
  }
  function getInFlightTaskId() {
    return GM_getValue("outreach_in_flight_task_id", "");
  }
  function setInFlightTaskId(id) {
    GM_setValue("outreach_in_flight_task_id", id || "");
    // Also stamp the URL we were on when we became busy with this task.
    if (id) {
      GM_setValue("outreach_in_flight_url", window.location.href);
      GM_setValue("outreach_in_flight_started_at", Date.now());
    } else {
      GM_setValue("outreach_in_flight_url", "");
      GM_setValue("outreach_in_flight_started_at", 0);
    }
  }
  function getInFlightUrl() {
    return GM_getValue("outreach_in_flight_url", "");
  }
  function getInFlightAgeMs() {
    const ts = GM_getValue("outreach_in_flight_started_at", 0);
    return ts ? (Date.now() - ts) : 0;
  }

  // ── DOM helpers (verbatim from paper oracle v4.10) ───────────────────

  function findPromptInput() {
    for (const sel of [
      "#prompt-textarea",
      "div.ProseMirror[contenteditable='true']",
      "[id='prompt-textarea']",
      "div[contenteditable='true'][role='textbox']",
      "div[contenteditable='true']",
    ]) {
      const el = document.querySelector(sel);
      if (el) return el;
    }
    return null;
  }

  function findSendButton(allowDisabled = false) {
    for (const sel of [
      "button[data-testid='send-button']",
      "button[data-testid='composer-send-button']",
      "button[aria-label='Send prompt']",
      "button[aria-label='发送提示']",
      "button[aria-label='Send']",
      "button[aria-label='Send message']",
      "button[aria-label='Submit']",
    ]) {
      const el = document.querySelector(sel);
      if (el && (allowDisabled || !el.disabled)) return el;
    }
    for (const btn of document.querySelectorAll("button[data-testid]")) {
      const tid = btn.getAttribute("data-testid") || "";
      if (tid.toLowerCase().includes("send") && (allowDisabled || !btn.disabled)) return btn;
    }
    function isNonSendButton(btn) {
      const tid = (btn.getAttribute("data-testid") || "").toLowerCase();
      const label = (btn.getAttribute("aria-label") || "").toLowerCase();
      const text = (btn.textContent || "").toLowerCase();
      const all = tid + " " + label + " " + text;
      return /plus|attach|file|添加|文件|mic|voice|听写|dictation|new|model|专业|search|搜索/.test(all);
    }
    const formAreas = [
      document.querySelector("form"),
      document.querySelector("[class*='composer']"),
      document.querySelector("[class*='input-area']"),
      document.querySelector("[class*='prompt']")?.closest("div[class]"),
    ].filter(Boolean);
    for (const area of formAreas) {
      for (const btn of area.querySelectorAll("button:not([disabled])")) {
        if (isNonSendButton(btn)) continue;
        const svg = btn.querySelector("svg");
        if (svg) {
          const paths = svg.querySelectorAll("path, polyline, line");
          if (paths.length > 0 && paths.length < 5) {
            const rect = btn.getBoundingClientRect();
            if (rect.width > 0 && rect.height > 0) return btn;
          }
        }
      }
    }
    const promptInput = findPromptInput();
    if (promptInput) {
      let container = promptInput.parentElement;
      for (let depth = 0; depth < 6 && container; depth++) {
        const btns = container.querySelectorAll("button:not([disabled])");
        for (const btn of btns) {
          if (isNonSendButton(btn)) continue;
          if (btn.querySelector("svg")) return btn;
        }
        container = container.parentElement;
      }
    }
    return null;
  }

  function isOnNewChatPage() {
    const msgs = document.querySelectorAll("[data-message-author-role]");
    return msgs.length === 0;
  }

  // OUTREACH ADD: detect if current page is a /c/<id> conversation
  function currentChatUrl() {
    const href = window.location.href;
    if (/\/c\/[a-f0-9-]{6,}/.test(href)) return href.split("?")[0];
    return "";
  }

  // OUTREACH ADD: ChatGPT 5.5 redirects /?outreach=1 → /c/<latest>, so URL
  // navigation to fresh chat fails. Click the in-page "New Chat" button instead;
  // this is an SPA transition the app handles cleanly.
  function findNewChatButton() {
    for (const sel of [
      "button[data-testid='new-chat-button']",
      "a[data-testid='new-chat-button']",
      "button[aria-label='New chat']",
      "button[aria-label='New Chat']",
      "button[aria-label='新聊天']",
      "button[aria-label='新建聊天']",
      "a[href='/']",
      "a[href='/?model=']",
      "[data-testid='create-new-chat-button']",
      "[data-testid='create-new-chat']",
    ]) {
      const el = document.querySelector(sel);
      if (el) return el;
    }
    // Fallback: scan sidebar for an element with text content "New chat" / "新聊天"
    for (const el of document.querySelectorAll("a, button")) {
      const txt = (el.textContent || "").trim();
      if (/^(\+\s*)?(New chat|New Chat|新聊天|新建聊天)$/i.test(txt)) return el;
    }
    return null;
  }

  async function clickNewChatButton() {
    const btn = findNewChatButton();
    if (!btn) return false;
    btn.click();
    await sleep(2000); // SPA transition settle
    // Verify we landed on fresh chat
    return isOnNewChatPage();
  }

  // ── Enter prompt (verbatim) ──────────────────────────────────────────
  async function enterPrompt(text) {
    log(`Entering prompt (${text.length} chars)...`);
    const input = findPromptInput();
    if (!input) { log("ERROR: prompt input not found"); return false; }
    input.focus();
    await sleep(300);
    document.execCommand("selectAll", false, null);
    document.execCommand("delete", false, null);
    await sleep(200);
    let success = false;
    try {
      input.focus();
      const CHUNK = 4000;
      if (text.length <= CHUNK) {
        document.execCommand("insertText", false, text);
      } else {
        for (let i = 0; i < text.length; i += CHUNK) {
          document.execCommand("insertText", false, text.slice(i, i + CHUNK));
          await sleep(50);
        }
      }
      await sleep(500);
      if ((input.textContent || "").length > 10) {
        success = true;
        log("Prompt: inserted via execCommand (ProseMirror-native)");
      }
    } catch (e) { log(`execCommand failed: ${e.message}`); }
    if (!success) {
      try {
        await navigator.clipboard.writeText(text);
        input.focus();
        document.execCommand("paste");
        await sleep(500);
        if ((input.textContent || "").length > 10) {
          success = true;
          log("Prompt: pasted via clipboard API");
        }
      } catch (e) { log(`Clipboard paste failed: ${e.message}`); }
    }
    if (!success) {
      try {
        const clipData = new DataTransfer();
        clipData.setData("text/plain", text);
        input.dispatchEvent(new ClipboardEvent("paste", {
          bubbles: true, cancelable: true, clipboardData: clipData,
        }));
        await sleep(500);
        if ((input.textContent || "").length > 10) {
          success = true;
          log("Prompt: pasted via synthetic ClipboardEvent");
        }
      } catch (e) { log(`Synthetic paste failed: ${e.message}`); }
    }
    if (!success) {
      const escaped = text.replace(/&/g, "&amp;").replace(/</g, "&lt;")
                          .replace(/>/g, "&gt;").replace(/\n/g, "<br>");
      input.innerHTML = `<p>${escaped}</p>`;
      input.dispatchEvent(new InputEvent("input", {
        bubbles: true, cancelable: true, inputType: "insertText", data: text,
      }));
      input.dispatchEvent(new Event("change", { bubbles: true }));
      await sleep(500);
      log("Prompt: set via innerHTML (last resort)");
      success = (input.textContent || "").length > 0;
    }
    if (success) {
      input.focus();
      const sel = window.getSelection();
      if (sel) { sel.selectAllChildren(input); sel.collapseToEnd(); }
      document.execCommand("insertText", false, " ");
      await sleep(300);
      document.execCommand("delete", false, null);
      await sleep(300);
      log("Prompt: forced React sync (space+delete)");
    }
    const visible = (input.textContent || "").length;
    log(`Prompt visible: ${visible} chars, success=${success}`);
    return success;
  }

  // ── Click send (verbatim) ────────────────────────────────────────────
  async function clickSend() {
    await sleep(1000);
    log("Waiting for send button to be ready...");
    for (let i = 0; i < 60; i++) {
      const btn = findSendButton();
      if (btn && !btn.disabled) {
        const tid = btn.getAttribute("data-testid");
        const lbl = btn.getAttribute("aria-label");
        log(`Send button found (testid=${tid}, label=${lbl}), clicking ONCE...`);
        btn.click();
        await sleep(500);
        return true;
      }
      if (i > 0 && i % 5 === 0) {
        const inp = findPromptInput();
        if (inp) {
          inp.dispatchEvent(new InputEvent("input", { bubbles: true, inputType: "insertText" }));
          inp.dispatchEvent(new Event("change", { bubbles: true }));
        }
        log(`Send button still disabled... ${i * 0.5}s, retrying input event`);
      }
      await sleep(500);
    }
    const disabledSend = findSendButton(true);
    if (disabledSend) {
      log(`Force-clicking disabled send button`);
      disabledSend.disabled = false;
      disabledSend.removeAttribute("disabled");
      await sleep(100);
      disabledSend.click();
      await sleep(500);
      const inp = findPromptInput();
      const promptCleared = !inp || (inp.textContent || "").trim().length < 10;
      const stopBtn = document.querySelector("button[data-testid='stop-button']");
      if (promptCleared || stopBtn) { log("Force-click appears to have worked"); return true; }
    }
    const input = findPromptInput();
    if (input) {
      log("Send: trying Enter key...");
      input.focus();
      await sleep(100);
      for (const evtType of ["keydown", "keypress", "keyup"]) {
        input.dispatchEvent(new KeyboardEvent(evtType, {
          key: "Enter", code: "Enter", keyCode: 13, which: 13,
          bubbles: true, cancelable: true,
        }));
        await sleep(50);
      }
      await sleep(500);
      const remaining = (input.textContent || "").trim();
      if (remaining.length < 10) {
        log("Send: Enter key worked (prompt cleared)");
        return true;
      }
    }
    log("ERROR: cannot send after retries");
    return false;
  }

  // ── Response extraction (verbatim from paper oracle v4.10) ───────────
  let sentPromptText = "";
  let postSendLines = new Set();

  function setSentPrompt(text) { sentPromptText = text; }

  function looksLikePromptEcho(text) {
    if (!sentPromptText || sentPromptText.length < 20) return false;
    const t = text.trim();
    if (/^(你说|You said)/i.test(t)) return true;
    const stripped = t
      .replace(/^(你说|You said)[：:]?\s*/i, "")
      .replace(/^main(\.pdf)?\s*/i, "")
      .replace(/^PDF\s*/i, "")
      .trim();
    const promptStart = sentPromptText.slice(0, 80).trim();
    if (stripped.length > 0
        && stripped.startsWith(promptStart)
        && stripped.length <= sentPromptText.length * 1.1) {
      return true;
    }
    if (t.length > 50
        && t.length < sentPromptText.length * 1.3
        && t.length > sentPromptText.length * 0.7) {
      const chunks = sentPromptText.match(/.{50}/g) || [];
      if (chunks.length > 10) {
        const hits = chunks.filter(c => t.includes(c)).length;
        if (hits / chunks.length > 0.8) return true;
      }
    }
    return false;
  }

  function capturePostSendState() {
    const main = document.querySelector("main");
    const text = main ? (main.innerText || "").trim() : "";
    postSendLines = new Set(text.split("\n").map(l => l.trim()).filter(l => l.length > 0));
    log(`Post-send captured: ${postSendLines.size} lines`);
  }

  const CHROME_RE = [
    /^(进阶专业|ChatGPT\s*也可能会犯错|请核查重要信息|查看\s*Cookie|Cookie\s*首选项)/,
    /^(ChatGPT can make mistakes|Check important info)/,
    /^Extended\s*Pro$/i,
    /^(Deep research|Deep thinking|Reasoning)$/i,
    /^Thought for \d+/,
    /^(你说|You said|ChatGPT\s*说|ChatGPT\s*said)[：:]?\s*$/,
    /^(正在思考|正在搜索|Searching)/,
    /^main(\.pdf)?\s*$/,
    /^PDF\s*$/,
    /^(进阶专业模式|click to remove|Start dictation|Send prompt)/,
    /^(新建聊天|New chat|搜索聊天|Search chats|图片|Images)/,
    /^(查看方案|See plans|设置|Settings|帮助|Help)/,
    /^(获取根据保存的聊天量身定制的回复|Get responses tailored)/,
    /^(登录|Log in|注册|Sign up)/,
    /^(我们使用\s*cookie|We use cookies|管理\s*Cookie|Manage Cookies)/,
    /^(拒绝非必要|Reject non-essential|接受所有|Accept all)/,
    /^See Cookie Preferences/,
  ];
  // OUTREACH FIX 2026-04-30: SSR markers were being matched against the WHOLE
  // extracted response, causing any review that contained those strings (e.g.
  // a critique of our own code) to be rejected forever. Now: cleanText strips
  // SSR boot lines first, isSSRGarbage only fires for SHORT responses.
  const SSR_GARBAGE_RE = /window\.__oai_log|window\.__oai_SSR|requestAnimationFrame/;
  const SSR_LINE_RE = /window\.__oai_(log|SSR)\s*[=(]|requestAnimationFrame\s*\(/;

  function isChromeLine(t) {
    if (!t || t.length > 200) return false;
    return CHROME_RE.some(re => re.test(t));
  }

  function isSsrLine(t) {
    if (!t || t.length > 400) return false;
    return SSR_LINE_RE.test(t);
  }

  function cleanText(text) {
    return text.split("\n").filter(line => {
      const t = line.trim();
      if (!t) return true;
      if (isChromeLine(t)) return false;
      if (isSsrLine(t)) return false;
      return true;
    }).join("\n").trim();
  }

  function extractTextWithMath(el) {
    if (!el) return "";
    const clone = el.cloneNode(true);
    for (const ann of Array.from(
        clone.querySelectorAll('annotation[encoding="application/x-tex"]'))) {
      const latex = (ann.textContent || "").trim();
      if (!latex) continue;
      const katexOuter = ann.closest(".katex-display, .katex") || ann.parentElement;
      if (katexOuter) {
        const isDisplay = katexOuter.classList.contains("katex-display") ||
                          (katexOuter.parentElement &&
                           katexOuter.parentElement.classList.contains("katex-display"));
        const wrapped = isDisplay ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        katexOuter.replaceWith(document.createTextNode(wrapped));
      }
    }
    for (const mjx of Array.from(clone.querySelectorAll("mjx-container"))) {
      let latex = "";
      const mmlAnn = mjx.querySelector('annotation[encoding*="TeX"]');
      if (mmlAnn) latex = (mmlAnn.textContent || "").trim();
      if (!latex) latex = mjx.getAttribute("aria-label") || "";
      if (!latex) latex = mjx.getAttribute("data-latex") || "";
      if (latex) {
        const isDisplay = mjx.getAttribute("display") === "true" ||
                          mjx.getAttribute("data-display") === "block";
        const wrapped = isDisplay ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        mjx.replaceWith(document.createTextNode(wrapped));
      }
    }
    for (const mathEl of Array.from(
        clone.querySelectorAll("[data-math-tex], [data-tex], [data-latex]"))) {
      const latex = mathEl.getAttribute("data-math-tex") ||
                    mathEl.getAttribute("data-tex") ||
                    mathEl.getAttribute("data-latex") || "";
      if (latex) {
        const isBlock = mathEl.tagName.toLowerCase() === "div" ||
                        mathEl.getAttribute("display") === "block";
        const wrapped = isBlock ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        mathEl.replaceWith(document.createTextNode(wrapped));
      }
    }
    for (const math of Array.from(clone.querySelectorAll("math"))) {
      if (!math.isConnected) continue;
      const alttext = math.getAttribute("alttext") || "";
      if (alttext) math.replaceWith(document.createTextNode(` $${alttext}$ `));
    }
    return (clone.innerText || "").trim();
  }

  function isSSRGarbage(text) {
    if (!text || text.length < 10) return false;
    // OUTREACH FIX: only flag short responses that are dominated by SSR
    // boot markers. A long response (>= 500 chars) that happens to contain
    // "window.__oai_log" inside a code block or critique is NOT garbage.
    if (text.length >= 500) return false;
    // Short response: check for multiple SSR markers OR very high JS density.
    const ssrHits = (text.match(/window\.__oai_/g) || []).length;
    if (ssrHits >= 2) return true;
    const jsRatio = (text.match(/[{}();=]/g) || []).length / text.length;
    if (jsRatio > 0.15) return true;
    return false;
  }

  // OUTREACH ADD: dedicated extraction targeting only assistant-role DOM.
  // For re_extract mode we know the conversation has at least one assistant
  // turn we want; this skips the heuristic gauntlet and goes straight to it.
  function extractAssistantOnly() {
    const main = document.querySelector("main");
    if (!main) return "";
    const els = main.querySelectorAll("[data-message-author-role='assistant']");
    if (els.length === 0) return "";
    // Walk from last to first; pick the largest substantive one
    const candidates = [];
    for (let i = els.length - 1; i >= 0; i--) {
      const text = cleanText(extractTextWithMath(els[i]));
      if (text.length >= 100 && !looksLikePromptEcho(text)) {
        candidates.push({ idx: i, text, len: text.length });
      }
    }
    if (candidates.length === 0) return "";
    // Return the LAST (most recent) one
    candidates.sort((a, b) => b.idx - a.idx);
    return candidates[0].text;
  }

  function extractResponseText() {
    const main = document.querySelector("main");
    if (!main) return "";
    const fullText = extractTextWithMath(main);

    if (sentPromptText.length > 500) {
      const tailAnchor = sentPromptText.slice(-100).trim();
      let idx = fullText.lastIndexOf(tailAnchor);
      if (idx < 0 && tailAnchor.length > 50) idx = fullText.lastIndexOf(tailAnchor.slice(-50));
      if (idx >= 0) {
        const after = cleanText(fullText.slice(idx + tailAnchor.length));
        if (after.length > 100) return after;
      }
    }

    const candidates = [];
    const allBlocks = main.querySelectorAll("div, article, section");
    for (const el of allBlocks) {
      const text = extractTextWithMath(el);
      if (text.length < 200) continue;
      candidates.push({ el, text, len: text.length });
    }
    candidates.sort((a, b) => b.len - a.len);
    for (const cand of candidates) {
      const cleaned = cleanText(cand.text);
      if (cleaned.length < 200) continue;
      const pageLen = fullText.length;
      if (cleaned.length > pageLen * 0.95 && candidates.length > 3) continue;
      if (looksLikePromptEcho(cleaned)) continue;
      if (sentPromptText.length > 500) {
        const promptStart = sentPromptText.slice(0, 200).trim();
        if (cleaned.startsWith(promptStart)
            && cleaned.length <= sentPromptText.length * 1.1) continue;
      }
      return cleaned;
    }

    const s0Selectors = [
      "[data-message-author-role='assistant']",
      "[data-testid*='conversation-turn']",
      "article",
      "div[class*='markdown']",
      "div[class*='prose']",
      "div.markdown",
      "[class*='agent-turn']",
    ];
    for (const sel of s0Selectors) {
      try {
        const els = document.querySelectorAll(sel);
        if (els.length === 0) continue;
        for (let i = els.length - 1; i >= 0; i--) {
          const text = extractTextWithMath(els[i]);
          const cleaned = cleanText(text);
          if (cleaned.length < 200) continue;
          if (looksLikePromptEcho(cleaned)) continue;
          if (sentPromptText.length > 30) {
            const ps = sentPromptText.slice(0, 40).trim();
            if (cleaned.startsWith(ps) && cleaned.length < sentPromptText.length * 1.2) continue;
          }
          return cleaned;
        }
      } catch {}
    }

    if (fullText.length < 100) return "";
    if (sentPromptText.length > 30) {
      for (const anchorLen of [80, 50, 30]) {
        const anchor = sentPromptText.slice(0, anchorLen).trim();
        const idx = fullText.indexOf(anchor);
        if (idx >= 0) {
          let endIdx = idx + sentPromptText.length;
          if (sentPromptText.length > 60) {
            const tail = sentPromptText.slice(-40).trim();
            const tailIdx = fullText.indexOf(tail, idx);
            if (tailIdx >= 0) endIdx = Math.max(endIdx, tailIdx + tail.length);
          }
          const after = cleanText(fullText.slice(endIdx));
          if (after.length > 100) return after;
        }
      }
    }

    if (postSendLines.size > 0) {
      const newLines = fullText.split("\n").filter(l => {
        const t = l.trim();
        return t.length > 0 && !postSendLines.has(t) && !isChromeLine(t);
      });
      if (newLines.length > 3) {
        const diffText = newLines.join("\n").trim();
        if (diffText.length > 100 && !looksLikePromptEcho(diffText)) return diffText;
      }
    }
    return "";
  }

  function isStillGenerating() {
    const domSignal = !!(
      document.querySelector("button[aria-label='Stop generating']") ||
      document.querySelector("button[aria-label='Stop streaming']") ||
      document.querySelector("button[aria-label='停止生成']") ||
      document.querySelector("button[aria-label='停止流式传输']") ||
      document.querySelector("button[data-testid='stop-button']") ||
      document.querySelector("[class*='result-streaming']") ||
      document.querySelector("[class*='streaming']") ||
      document.querySelector("[class*='thinking']") ||
      document.querySelector("[class*='reasoning']") ||
      document.querySelector("[class*='progress']")
    );
    if (domSignal) return true;
    // Text-layer probe for ChatGPT 5.5 Pro reasoning indicators that don't
    // expose stable class hooks. The page text contains these literals while
    // the Pro reasoner is still thinking and before the visible answer
    // streams in. Without this fallback the userscript trips on "Pro thinking"
    // pages that look stable but are mid-generation. (Fix: T-20 Turn 2.)
    try {
      const main = document.querySelector("main");
      if (!main) return false;
      const txt = main.innerText || "";
      // "Pro thinking" — ChatGPT 5.5 Pro reasoning state preamble
      // "Extended Pro" — appears in reasoner footer DURING reasoning, not after
      // "Thought for" — only appears AFTER reasoning completes (post-think)
      // We treat the page as still generating if the reasoning preamble is
      // present AND the post-think marker "Thought for" is NOT yet visible,
      // since "Thought for X min Ys" appears once reasoning is done and the
      // answer starts streaming.
      const proPreamble = /Pro thinking|Extended Pro|Reasoning…/i.test(txt);
      const postThink = /Thought for\s+\d+(?:\s*m\s*\d+\s*s|\s*s|\s+min)/i.test(txt);
      if (proPreamble && !postThink) return true;
    } catch {}
    return false;
  }

  async function waitForResponse() {
    log("Waiting for ChatGPT response...");
    const startTime = Date.now();
    let lastText = "";
    let stableCount = 0;
    let lastLogTime = 0;
    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);
      const responseText = extractResponseText();
      const generating = isStillGenerating();
      const elapsed = Math.floor((Date.now() - startTime) / 1000);
      const mainLen = (document.querySelector("main")?.innerText || "").length;
      if (elapsed - lastLogTime >= 300) {
        lastLogTime = elapsed;
        log(`Wait: ${elapsed}s, extracted=${responseText.length}, page=${mainLen}, stable=${stableCount}, gen=${generating}, url=${window.location.href.slice(-30)}`);
      }
      if (responseText.length >= 5) {
        if (looksLikePromptEcho(responseText)) {
          if (stableCount === 0) log(`Prompt echo detected (${responseText.length} chars) — waiting`);
          stableCount = 0; lastText = ""; continue;
        }
        if (isSSRGarbage(responseText)) {
          if (stableCount === 0) log(`SSR garbage detected — page hydrating, waiting`);
          stableCount = 0; lastText = ""; continue;
        }
        if (responseText === lastText) {
          stableCount++;
          let minChecks;
          if (responseText.length >= 2000) minChecks = STABLE_CHECKS;
          else if (responseText.length >= 200) minChecks = STABLE_CHECKS + 2;
          else minChecks = STABLE_CHECKS * 3;
          const stableEnough = stableCount >= minChecks && !generating;
          const stableOverride = stableCount >= minChecks + 3;
          if (stableEnough || stableOverride) {
            log(`Response complete: ${responseText.length} chars (stable ${stableCount * STABLE_INTERVAL / 1000}s, gen=${generating})`);
            return responseText;
          }
        } else {
          stableCount = 0;
          lastText = responseText;
        }
      } else if (generating) {
        stableCount = 0;
      }
    }
    log(`TIMEOUT (${MAX_WAIT/1000}s), returning partial: ${lastText.length} chars`);
    return lastText;
  }

  // ── Process a task (OUTREACH ADD: multi-turn navigation + reload-safe) ─
  async function processTask(task) {
    const { task_id, prompt, conversation_url, is_followup, conversation_id, re_extract } = task;
    busy = true;
    updatePanel();

    // OUTREACH ADD: re_extract mode. Server says "this conversation already
    // has the response we want — just navigate there and extract the latest
    // assistant message, do not enter or send anything". Used to recover
    // from earlier extraction failures (SSR false-positive, premature timeout).
    if (re_extract) {
      log(`=== Task: ${task_id} [RE-EXTRACT] conv=${(conversation_id || "").slice(0, 12)} ===`);
      try {
        if (conversation_url && !window.location.href.startsWith(conversation_url)) {
          GM_setValue("outreach_navigating", true);
          GM_setValue("outreach_nav_task_id", task_id);
          saveTaskState(task);
          setTaskPhase("navigating");
          log(`Navigating to ${conversation_url.slice(-60)} for re-extract ...`);
          busy = false;
          updatePanel();
          window.location.href = conversation_url;
          return;
        }
        try { await serverPost("/ack", { task_id, agent_id: agentId() }); } catch {}
        await sleep(3000); // settle DOM
        if (prompt) setSentPrompt(prompt);
        // OUTREACH ADD: try dedicated assistant-only extraction first (bypasses
        // heuristics that can fall to prompt echo when sentPromptText isn't
        // perfectly aligned). Fall back to extractResponseText if none found.
        let response = extractAssistantOnly();
        if (!response || response.length < 100) {
          log(`re-extract: assistant-only got ${response?.length || 0} chars; falling back to extractResponseText`);
          response = extractResponseText();
        } else {
          log(`re-extract: assistant-only got ${response.length} chars`);
        }
        if (!response || response.length < 100) {
          throw new Error(`re-extract: nothing meaningful (${response?.length || 0} chars)`);
        }
        const chatUrl = currentChatUrl();
        await serverPost("/result", {
          task_id, response, chatgpt_url: chatUrl,
          agent_id: agentId(), model: task.model || "unknown",
        });
        log(`DONE (re-extract): ${task_id} (${response.length} chars)`);
        clearTaskState();
        setInFlightTaskId("");
      } catch (err) {
        log(`ERROR (re-extract): ${err.message}`);
        try {
          await serverPost("/result", {
            task_id, response: `ERROR (re-extract): ${err.message}`,
            chatgpt_url: currentChatUrl(), agent_id: agentId(),
            model: task.model || "unknown",
          });
        } catch {}
        clearTaskState();
        setInFlightTaskId("");
      } finally {
        busy = false;
        updatePanel();
      }
      return;
    }

    // OUTREACH ADD: re-entry guard. If this same task_id is in flight and we
    // are currently on a /c/<uuid> page (= ChatGPT already accepted our first
    // prompt and started generating), DO NOT re-enter the prompt. Just resume
    // waitForResponse. ChatGPT 5.5 triggers a full page reload when the URL
    // first changes from chatgpt.com/ to chatgpt.com/c/<uuid>, which loses
    // our in-memory state but the in-flight task survives.
    const onConvPage = /\/c\/[a-f0-9-]{6,}/.test(window.location.href);
    if (getInFlightTaskId() === task_id && onConvPage && !is_followup) {
      log(`=== Task: ${task_id} [RESUMING on existing chat ${currentChatUrl().slice(-40)}] ===`);
      try { await serverPost("/ack", { task_id, agent_id: agentId() }); } catch {}
      setTaskPhase("processing");
      setSentPrompt(prompt);
      capturePostSendState();
      try {
        const response = await waitForResponse();
        if (!response || response.length < 5) {
          throw new Error(`Resumed wait got no response (${response?.length || 0} chars)`);
        }
        const chatUrl = currentChatUrl();
        log(`Resumed chat URL captured: ${chatUrl.slice(-50) || "(none)"}`);
        await serverPost("/result", {
          task_id, response, chatgpt_url: chatUrl,
          agent_id: agentId(), model: task.model || "unknown",
        });
        log(`DONE (resumed): ${task_id} (${response.length} chars)`);
        clearTaskState();
        setInFlightTaskId("");
      } catch (err) {
        log(`ERROR (resumed): ${err.message}`);
        try {
          await serverPost("/result", {
            task_id, response: `ERROR (resumed): ${err.message}`,
            chatgpt_url: currentChatUrl(), agent_id: agentId(),
            model: task.model || "unknown",
          });
        } catch {}
        clearTaskState();
        setInFlightTaskId("");
      } finally {
        busy = false;
        updatePanel();
      }
      return;
    }

    log(`=== Task: ${task_id} ${is_followup ? "[FOLLOW-UP]" : "[NEW]"} conv=${(conversation_id || "").slice(0, 12)} ===`);

    try {
      // OUTREACH ADD: navigation logic — three cases
      // (a) follow-up + conversation_url provided + we are NOT on it → navigate there
      // (b) new task + we're not on a fresh chat page → navigate to fresh chat
      // (c) otherwise stay where we are
      const targetUrl = (is_followup && conversation_url) ? conversation_url : null;
      const needNavToConv = targetUrl && !window.location.href.startsWith(targetUrl);
      const needNavToFresh = !targetUrl && !isOnNewChatPage();

      if (needNavToFresh) {
        // OUTREACH ADD: prefer in-page "New Chat" button click (SPA, no
        // redirect), fall back to URL navigation only if no button found.
        log(`Need fresh chat. Current URL: ${window.location.href.slice(-60)}`);
        const ok = await clickNewChatButton();
        if (ok) {
          log(`Clicked New Chat button; on fresh chat now.`);
          // No reload — keep going in same script instance
        } else {
          log(`No New Chat button found; falling back to URL navigation`);
          GM_setValue("outreach_navigating", true);
          GM_setValue("outreach_nav_task_id", task_id);
          saveTaskState(task);
          setTaskPhase("navigating");
          busy = false;
          updatePanel();
          window.location.href = "https://chatgpt.com/?outreach=1";
          return;
        }
      } else if (needNavToConv) {
        GM_setValue("outreach_navigating", true);
        GM_setValue("outreach_nav_task_id", task_id);
        saveTaskState(task);
        setTaskPhase("navigating");
        log(`Navigating to existing conv ${(targetUrl || "").slice(-60)} ...`);
        busy = false;
        updatePanel();
        window.location.href = targetUrl;
        return;
      }

      // ACK
      try { await serverPost("/ack", { task_id, agent_id: agentId() }); } catch {}
      setTaskPhase("processing");
      // OUTREACH ADD: mark this task in-flight BEFORE we send. Also save the
      // task body so a full reload mid-flight can read prompt back without
      // hitting the server queue (which would trigger needNavToFresh again).
      setInFlightTaskId(task_id);
      saveTaskState(task);

      // Wait for prompt input. Bumped to 90s — ChatGPT 5.5 fresh chat can be
      // slow to hydrate, especially after a New Chat button click that
      // unmounts and remounts the composer. Log every 15s for visibility.
      let retries = 0;
      while (!findPromptInput() && retries < 90) {
        await sleep(1000);
        retries++;
        if (retries > 0 && retries % 15 === 0) {
          log(`Still waiting for prompt input... ${retries}s, url=${window.location.href.slice(-50)}`);
        }
      }
      if (!findPromptInput()) {
        throw new Error(`Prompt input not found after 90s (url=${window.location.href})`);
      }
      log(`Page ready (${is_followup ? "existing conv" : "fresh chat"}) after ${retries}s`);

      // Enter prompt
      const entered = await enterPrompt(prompt);
      if (!entered) throw new Error("Failed to enter prompt text");
      setSentPrompt(prompt);

      // Wait for send button
      log("Waiting for send button to enable...");
      let sendReady = false;
      for (let i = 0; i < 30; i++) {
        const btn = findSendButton();
        if (btn && !btn.disabled) { sendReady = true; log(`Send ready after ${i}s`); break; }
        await sleep(1000);
      }
      if (!sendReady) log("WARN: send still disabled after 30s, will force-click");

      const urlBefore = window.location.href;
      const sent = await clickSend();
      if (!sent) throw new Error("Failed to click send");

      // For new chat: wait for URL change to /c/<id>
      // For follow-up: URL should NOT change (we stay in same /c/<id>)
      log(`Sent. urlBefore=${urlBefore.slice(-40)}`);
      if (!is_followup) {
        let urlChanged = false;
        for (let i = 0; i < 60; i++) {
          await sleep(1000);
          if (window.location.href !== urlBefore) {
            urlChanged = true;
            log(`URL changed to: ${window.location.href.slice(-40)}`);
            break;
          }
          if (isStillGenerating()) { log("Generation detected (same page)"); break; }
        }
        if (!urlChanged && !isStillGenerating()) {
          log("WARN: URL did not change and no generation after 60s");
        }
      } else {
        // For follow-up: just wait for generation to start
        for (let i = 0; i < 30; i++) {
          await sleep(1000);
          if (isStillGenerating()) { log("Follow-up generation started"); break; }
        }
      }

      await sleep(5000); // settle DOM
      capturePostSendState();
      const response = await waitForResponse();

      if (!response || response.length < 5) {
        throw new Error(`Response too short or empty (${response?.length || 0} chars)`);
      }

      // OUTREACH ADD: capture chat URL for the server to pin to conversation_id
      const chatUrl = currentChatUrl();
      log(`Chat URL captured: ${chatUrl.slice(-50) || "(none)"}`);

      await serverPost("/result", {
        task_id,
        response,
        chatgpt_url: chatUrl,
        agent_id: agentId(),
        model: task.model || "unknown",
      });
      log(`DONE: ${task_id} (${response.length} chars)`);
      clearTaskState();
      setInFlightTaskId("");  // OUTREACH ADD
    } catch (err) {
      log(`ERROR: ${err.message}`);
      try {
        await serverPost("/result", {
          task_id, response: `ERROR: ${err.message}`,
          chatgpt_url: currentChatUrl(),
          agent_id: agentId(), model: task.model || "unknown",
        });
      } catch {}
      clearTaskState();
      setInFlightTaskId("");  // OUTREACH ADD
    } finally {
      busy = false;
      updatePanel();
    }
  }

  // OUTREACH ADD: agent_id is PER-TAB, not per-script.
  // GM_setValue is shared across all tabs that have this userscript installed,
  // so persisting agent_id there causes multiple tabs to share an identity and
  // the server dispatches the same task to all of them concurrently. Use
  // sessionStorage (per-tab) instead, fall back to window.name + URL flag.
  function agentId() {
    const m = window.location.search.match(/[?&]outreach=([^&]+)/);
    if (m) return `outreach_${m[1]}`;
    try {
      let stored = sessionStorage.getItem("outreach_agent_id");
      if (!stored) {
        stored = `outreach_${Math.floor(Math.random() * 9000) + 1000}_${Date.now().toString(36).slice(-4)}`;
        sessionStorage.setItem("outreach_agent_id", stored);
      }
      return stored;
    } catch {
      // Private mode / sessionStorage disabled — fall back to window.name
      if (!window.name || !window.name.startsWith("outreach_")) {
        window.name = `outreach_${Math.floor(Math.random() * 9000) + 1000}_${Date.now().toString(36).slice(-4)}`;
      }
      return window.name;
    }
  }

  // ── Main loop ────────────────────────────────────────────────────────
  function _readActive() {
    try { return sessionStorage.getItem("outreach_active") === "1"; }
    catch { return false; }
  }
  async function pollLoop() {
    while (true) {
      active = _readActive();
      if (active && !busy) {
        try {
          const task = await serverGet(`/task?agent=${encodeURIComponent(agentId())}`);
          if (task && task.task_id && task.status !== "idle") {
            if (!_readActive()) {
              log("Task available but PAUSED — skipping");
            } else {
              // OUTREACH ADD: if we already had an in-flight task and the
              // server is handing us the SAME task_id (which it does because
              // pending_tasks idempotency), processTask's resume guard will
              // pick up where we left off rather than restart.
              await processTask(task);
            }
          }
        } catch (err) {
          if (logHistory.length === 0 || !logHistory[logHistory.length-1].includes("unreachable")) {
            log(`Server unreachable (${SERVER})`);
          }
        }
      }
      await sleep(POLL_INTERVAL);
    }
  }

  // ── Bootstrap ────────────────────────────────────────────────────────
  async function init() {
    log(`Outreach Oracle Bridge ${SCRIPT_VERSION} loaded — ${active ? "ACTIVE" : "PAUSED"} — agent=${agentId()}`);

    const phase = getTaskPhase();
    const navTaskId = GM_getValue("outreach_nav_task_id", "");
    const outreachNav = GM_getValue("outreach_navigating", false);
    const urlHasFlag = window.location.search.includes("outreach=");
    const inFlightId = getInFlightTaskId();
    const inFlightAgeMin = Math.floor(getInFlightAgeMs() / 60000);

    // OUTREACH ADD: if we have an in-flight task that's clearly stuck (>3h),
    // give up — server's task_timeout (4h) hasn't kicked in yet but we don't
    // want to deadlock. Clear flags; pollLoop will get next task.
    if (inFlightId && inFlightAgeMin > 180) {
      log(`Stale in-flight ${inFlightId} (${inFlightAgeMin}m old) — clearing`);
      setInFlightTaskId("");
      clearTaskState();
    }

    // OUTREACH ADD: full-page-reload landing on /c/<uuid> with an in-flight
    // task means ChatGPT redirected us mid-task. The next pollLoop cycle
    // will receive the same task from the server (pending_tasks idempotency)
    // and processTask's RESUMING branch will take over. Self-report the URL
    // so the server can pin it to the conversation_id for future re-extracts.
    if (inFlightId && /\/c\/[a-f0-9-]/.test(window.location.href)) {
      log(`Detected mid-task reload on /c/<uuid>; in-flight=${inFlightId} (${inFlightAgeMin}m). pollLoop will resume.`);
      try {
        await serverPost("/pin-conv-url", {
          task_id: inFlightId,
          chatgpt_url: window.location.href.split("?")[0],
          agent_id: agentId(),
        });
      } catch {}
    }

    if (phase === "navigating" && navTaskId && (outreachNav || urlHasFlag)) {
      log(`Resuming after navigation for task: ${navTaskId}`);
      GM_setValue("outreach_nav_task_id", "");
      GM_setValue("outreach_navigating", false);
      const savedTask = loadTaskState();
      clearTaskState();

      if (urlHasFlag) {
        const cleanUrl = window.location.href.replace(/[?&]outreach=[^&]+/, "").replace(/\?$/, "");
        history.replaceState(null, "", cleanUrl);
      }

      await sleep(3000);

      // Prefer the saved task (preserves is_followup + conversation context).
      // Fall back to re-fetching if state was lost.
      let task = savedTask;
      if (!task || !task.task_id) {
        try {
          task = await serverGet(`/task?agent=${encodeURIComponent(agentId())}`);
        } catch (e) { log(`Re-fetch failed: ${e.message}`); }
      }
      if (task && task.task_id && task.status !== "idle") {
        log(`Resumed task: ${task.task_id} prompt=${task.prompt?.length || 0} chars followup=${!!task.is_followup}`);
        await processTask(task);
      } else {
        log("WARN: no task to resume after navigation");
      }
    } else if (phase === "navigating") {
      log("Clearing stale navigation state (user browsing, not outreach)");
      GM_setValue("outreach_nav_task_id", "");
      GM_setValue("outreach_navigating", false);
      clearTaskState();
    }

    pollLoop();
  }

  if (document.readyState === "complete") setTimeout(init, 2000);
  else window.addEventListener("load", () => setTimeout(init, 2000));
})();
