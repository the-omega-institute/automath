// ==UserScript==
// @name         ChatGPT Oracle Bridge (Windows)
// @namespace    omega-automath
// @version      5.4
// @description  Multi-agent oracle bridge — open chatgpt.com/?oracle=1|2|3 for parallel review tabs. User tabs (no ?oracle=) unaffected.
// @match        https://chatgpt.com/*
// @match        https://chat.openai.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @connect      localhost
// @connect      127.0.0.1
// @run-at       document-start
// ==/UserScript==

(function () {
  "use strict";

  const SERVER = "http://127.0.0.1:8765";
  const SCRIPT_VERSION = "5.4";
  const POLL_INTERVAL = 30000;    // poll server every 30 seconds
  const STABLE_CHECKS = 3;        // response must be stable for 3 checks
  const STABLE_INTERVAL = 60000;  // check every 60 seconds
  const MAX_WAIT = 7200000;       // 120 minutes
  const DEFAULT_MIN_RESPONSE_LENGTH = 1000;
  const REQUIRE_FOREGROUND_TO_CLAIM = false;

  // ── Multi-agent: detect agent_id from URL or sessionStorage ──────────
  // Open chatgpt.com/?oracle=1  → agent "oracle_1"
  // Open chatgpt.com/?oracle=2  → agent "oracle_2"
  // Open chatgpt.com (no param) → dormant, user's tab
  //
  // Runs at document-start so we read the URL before ChatGPT's SPA
  // router can strip the query parameter.
  function detectAgentId() {
    // 1. Current URL (works at document-start before SPA routing)
    const urlParam = new URLSearchParams(window.location.search).get("oracle");
    if (urlParam) {
      const id = `oracle_${urlParam}`;
      try { sessionStorage.setItem("oracle_agent_id", id); } catch {}
      return id;
    }
    // 2. Navigation entry — catches the original URL even if SPA already rewrote it
    try {
      const navEntries = performance.getEntriesByType("navigation");
      if (navEntries.length > 0) {
        const origUrl = new URL(navEntries[0].name);
        const origParam = origUrl.searchParams.get("oracle");
        if (origParam) {
          const id = `oracle_${origParam}`;
          try { sessionStorage.setItem("oracle_agent_id", id); } catch {}
          return id;
        }
      }
    } catch {}
    // 3. sessionStorage — persists across same-tab navigations (e.g. /c/{id})
    try {
      return sessionStorage.getItem("oracle_agent_id") || "";
    } catch { return ""; }
  }

  const AGENT_ID = detectAgentId();
  const IS_ORACLE_TAB = !!AGENT_ID;

  // Dormant mode: user's own ChatGPT tab — script does absolutely nothing
  if (!IS_ORACLE_TAB) return;

  // Agent-namespaced GM keys (shared storage, but unique per agent)
  const GM_KEY = (k) => `${k}_${AGENT_ID}`;

  let busy = false;
  let active = GM_getValue(GM_KEY("oracle_active"), true); // oracle tabs auto-start

  // ── Logging ──────────────────────────────────────────────────────────
  const logHistory = [];
  function log(msg) {
    const ts = new Date().toLocaleTimeString();
    const entry = `${ts} ${msg}`;
    console.log(`[oracle] ${entry}`);
    logHistory.push(entry);
    if (logHistory.length > 20) logHistory.shift();
    updatePanel();
  }

  function toggleActive() {
    active = !active;
    GM_setValue(GM_KEY("oracle_active"), active);
    log(active ? "ACTIVATED — polling will start" : "PAUSED");
    updatePanel();
  }

  // ── Status panel ─────────────────────────────────────────────────────
  let panel = null;
  function ensurePanel() {
    if (panel && document.body.contains(panel)) return;
    panel = document.createElement("div");
    panel.id = "oracle-panel";
    panel.style.cssText = `
      position: fixed; bottom: 12px; right: 12px; z-index: 99999;
      background: #1a1a2e; color: #0f0; font-family: monospace; font-size: 11px;
      padding: 8px 12px; border-radius: 6px; max-width: 420px; max-height: 300px;
      overflow-y: auto; box-shadow: 0 2px 12px rgba(0,0,0,0.5); opacity: 0.92;
      line-height: 1.4;
    `;
    document.body.appendChild(panel);
  }

  function updatePanel() {
    ensurePanel();
    const statusColor = active ? (busy ? "#ff0" : "#0f0") : "#f55";
    const statusText = active ? (busy ? "BUSY" : "ACTIVE") : "PAUSED";
    const btnText = active ? "⏸ Pause" : "▶ Start";
    const btnColor = active ? "#f55" : "#0f0";
    const agentLabel = AGENT_ID.replace("oracle_", "#");
    const lines = logHistory.slice(-10).map(l => `<div>${l}</div>`).join("");
    panel.innerHTML = `
      <div style="display:flex;justify-content:space-between;align-items:center">
        <b>[Oracle v${SCRIPT_VERSION} ${agentLabel}]</b>
        <span style="color:${statusColor};font-weight:bold">${statusText}</span>
        <button id="oracle-toggle" style="background:${btnColor};color:#000;border:none;border-radius:3px;padding:2px 8px;cursor:pointer;font-size:11px;font-weight:bold">${btnText}</button>
      </div>
      <hr style="border-color:#333;margin:4px 0">
      ${lines}`;
    const btn = document.getElementById("oracle-toggle");
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
        onerror: (e) => reject(new Error("network error")),
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
        onerror: (e) => reject(new Error("network error")),
        ontimeout: () => reject(new Error("timeout")),
      });
    });
  }

  function foregroundState() {
    return `visibility=${document.visibilityState}, focus=${document.hasFocus()}`;
  }

  function isForegroundReady() {
    if (!REQUIRE_FOREGROUND_TO_CLAIM) return true;
    return document.visibilityState === "visible" && document.hasFocus();
  }

  async function postPhase(task_id, phase, detail = "") {
    try {
      await serverPost("/phase", { task_id, agent_id: AGENT_ID, phase, detail });
    } catch {}
  }

  async function releaseTask(task_id, reason) {
    log(`Releasing task before send: ${reason}`);
    try {
      await serverPost("/release", { task_id, agent_id: AGENT_ID, reason });
    } catch (e) {
      log(`Release failed: ${e.message}`);
    }
    clearTaskState();
    busy = false;
    updatePanel();
  }

  function sleep(ms) {
    return new Promise((r) => setTimeout(r, ms));
  }

  // ── Persistent task state (survives page navigation, namespaced per agent) ──
  function saveTaskState(task) {
    GM_setValue(GM_KEY("current_task"), JSON.stringify(task));
    GM_setValue(GM_KEY("task_phase"), "pending");
  }
  function loadTaskState() {
    try {
      const s = GM_getValue(GM_KEY("current_task"), "");
      return s ? JSON.parse(s) : null;
    } catch { return null; }
  }
  function getTaskPhase() {
    return GM_getValue(GM_KEY("task_phase"), "");
  }
  function setTaskPhase(phase) {
    GM_setValue(GM_KEY("task_phase"), phase);
  }
  function clearTaskState() {
    GM_setValue(GM_KEY("current_task"), "");
    GM_setValue(GM_KEY("task_phase"), "");
  }

  // ── DOM helpers for ChatGPT UI ───────────────────────────────────────

  function isUsablePromptInput(el) {
    if (!el) return false;
    const style = window.getComputedStyle(el);
    if (style.display === "none" || style.visibility === "hidden") return false;
    const rect = el.getBoundingClientRect();
    if (rect.width < 40 || rect.height < 12) return false;
    const disabled = el.getAttribute("aria-disabled") === "true" || el.disabled;
    return !disabled;
  }

  function findPromptInput() {
    // ChatGPT 2024-2026 uses ProseMirror/contenteditable composer variants.
    for (const sel of [
      "#prompt-textarea",
      "textarea#prompt-textarea",
      "textarea[data-testid='prompt-textarea']",
      "[data-testid='prompt-textarea']",
      "[data-testid='composer-text-input']",
      "div.ProseMirror[contenteditable='true']",
      "div.ProseMirror[contenteditable='plaintext-only']",
      "[id='prompt-textarea']",
      "div[contenteditable='true'][role='textbox']",
      "div[contenteditable='plaintext-only'][role='textbox']",
      "[role='textbox'][contenteditable]",
      "[aria-label='Ask anything']",
      "[aria-label='Message ChatGPT']",
      "form textarea",
      "main form textarea",
      "main form [contenteditable='true']",
      "main form [contenteditable='plaintext-only']",
      "div[contenteditable='true']",
      "div[contenteditable='plaintext-only']",
    ]) {
      for (const el of document.querySelectorAll(sel)) {
        if (isUsablePromptInput(el)) return el;
      }
    }
    const active = document.activeElement;
    if (active && active.matches && active.matches("[contenteditable], textarea")) {
      if (isUsablePromptInput(active)) return active;
    }
    return null;
  }

  function findSendButton(allowDisabled = false) {
    // Layer 1: Exact data-testid / aria-label selectors (updated 2025-2026)
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

    // Layer 2: Find by partial data-testid containing "send"
    for (const btn of document.querySelectorAll("button[data-testid]")) {
      const tid = btn.getAttribute("data-testid") || "";
      if (tid.toLowerCase().includes("send") && (allowDisabled || !btn.disabled)) return btn;
    }

    // Helper: is this button definitely NOT a send button?
    function isNonSendButton(btn) {
      const tid = (btn.getAttribute("data-testid") || "").toLowerCase();
      const label = (btn.getAttribute("aria-label") || "").toLowerCase();
      const text = (btn.textContent || "").toLowerCase();
      const all = tid + " " + label + " " + text;
      // Known non-send buttons in ChatGPT composer
      return /plus|attach|file|添加|文件|mic|voice|听写|dictation|new|model|专业|search|搜索/.test(all);
    }

    // Layer 3: Find SVG arrow icon inside form buttons (the send icon is typically an up-arrow)
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
            if (rect.width > 0 && rect.height > 0) {
              return btn;
            }
          }
        }
      }
    }

    // Layer 4: Any enabled button inside the prompt input's parent container
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

  function findFileInput() {
    // ChatGPT has a hidden file input
    return document.querySelector("input[type='file']");
  }

  function isOnNewChatPage() {
    // Check light DOM first
    const lightMsgs = document.querySelectorAll("[data-message-author-role]");
    if (lightMsgs.length > 0) return false;

    // Check Shadow DOM (ChatGPT 5.4 Pro renders messages there)
    for (const el of document.querySelectorAll("*")) {
      if (!el.shadowRoot) continue;
      const shadowMsgs = el.shadowRoot.querySelectorAll(
        "[data-message-author-role], [data-testid*='conversation-turn']"
      );
      if (shadowMsgs.length > 0) return false;
    }

    // Also check URL: /c/ in path means existing conversation
    if (/\/c\/[a-f0-9-]+/.test(window.location.pathname)) return false;

    return true;
  }

  // ── Wait for PDF upload to finish ─────────────────────────────────
  async function waitForUploadComplete(timeoutMs = 60000) {
    log("Waiting for PDF upload to complete...");
    const start = Date.now();

    while (Date.now() - start < timeoutMs) {
      await sleep(2000);

      // Check for upload progress indicators
      const uploading =
        document.querySelector("[class*='uploading']") ||
        document.querySelector("[class*='progress']") ||
        document.querySelector("[role='progressbar']") ||
        document.querySelector("[class*='loading']");

      // Check if an attachment chip/badge appeared (upload done)
      const attached =
        document.querySelector("[class*='attachment']") ||
        document.querySelector("[class*='file-chip']") ||
        document.querySelector("[data-testid*='attachment']") ||
        document.querySelector("[class*='uploaded']") ||
        document.querySelector("img[alt*='pdf']") ||
        document.querySelector("[class*='file']");

      const elapsed = Math.floor((Date.now() - start) / 1000);

      if (!uploading && attached) {
        log(`PDF upload complete (${elapsed}s), attachment visible`);
        return true;
      }

      // Also check: send button becomes enabled = upload done
      const sendBtn = findSendButton();
      if (sendBtn && !sendBtn.disabled && elapsed > 5) {
        log(`PDF upload likely complete (${elapsed}s), send button enabled`);
        return true;
      }

      if (elapsed % 10 === 0 && elapsed > 0) {
        log(`Upload waiting... ${elapsed}s (uploading=${!!uploading}, attached=${!!attached})`);
      }
    }

    log("Upload wait timeout — proceeding anyway");
    return false;
  }

  // ── Upload PDF ───────────────────────────────────────────────────────
  async function uploadPDF(base64Data, fileName) {
    log(`PDF upload: ${fileName} (${(base64Data.length * 0.75 / 1024).toFixed(0)} KB)`);

    // Convert base64 to File
    const byteChars = atob(base64Data);
    const byteArray = new Uint8Array(byteChars.length);
    for (let i = 0; i < byteChars.length; i++) {
      byteArray[i] = byteChars.charCodeAt(i);
    }
    const file = new File([byteArray], fileName, { type: "application/pdf" });

    let injected = false;

    // Method 1: Find hidden file input and inject
    const fileInput = findFileInput();
    if (fileInput) {
      try {
        const dt = new DataTransfer();
        dt.items.add(file);
        fileInput.files = dt.files;
        fileInput.dispatchEvent(new Event("change", { bubbles: true }));
        log("PDF: injected via file input");
        injected = true;
      } catch (e) {
        log(`PDF file input failed: ${e.message}`);
      }
    }

    // Method 2: Click the attachment button first, then use the file input
    if (!injected) {
      const attachBtn = document.querySelector(
        "button[aria-label='Attach files'], button[aria-label='Upload file'], " +
        "button[data-testid='composer-attach-button'], button[aria-haspopup='menu']"
      );
      if (attachBtn) {
        log("PDF: clicking attachment button...");
        attachBtn.click();
        await sleep(1000);

        const fi2 = document.querySelector("input[type='file']");
        if (fi2) {
          try {
            const dt2 = new DataTransfer();
            dt2.items.add(file);
            fi2.files = dt2.files;
            fi2.dispatchEvent(new Event("change", { bubbles: true }));
            log("PDF: injected after clicking attach");
            injected = true;
          } catch (e) {
            log(`PDF inject after attach failed: ${e.message}`);
          }
        }
      }
    }

    // Method 3: Drop event on the composer
    if (!injected) {
      log("PDF: trying drag-drop...");
      const dropTarget =
        document.querySelector("form") ||
        findPromptInput()?.closest("div") ||
        document.querySelector("[class*='composer']");

      if (dropTarget) {
        const dt3 = new DataTransfer();
        dt3.items.add(file);
        for (const evtType of ["dragenter", "dragover", "drop"]) {
          dropTarget.dispatchEvent(new DragEvent(evtType, {
            bubbles: true, cancelable: true, dataTransfer: dt3,
          }));
          await sleep(300);
        }
        log("PDF: drag-drop dispatched");
        injected = true;
      }
    }

    if (!injected) {
      log("PDF: ALL METHODS FAILED — continuing without PDF");
      return false;
    }

    // Wait for the upload to actually finish before proceeding
    await waitForUploadComplete(60000);
    return true;
  }

  // ── Enter prompt text into ProseMirror ───────────────────────────────
  async function enterPrompt(text) {
    log(`Entering prompt (${text.length} chars)...`);

    const input = findPromptInput();
    if (!input) {
      log("ERROR: prompt input not found");
      return false;
    }

    input.focus();
    await sleep(300);

    // Clear any existing content first
    document.execCommand("selectAll", false, null);
    document.execCommand("delete", false, null);
    await sleep(200);

    let success = false;

    // Strategy 1: execCommand insertText — BEST for ProseMirror
    // This goes through the browser's native editing API which ProseMirror hooks into,
    // so React/ProseMirror internal state stays in sync → send button enables correctly.
    try {
      input.focus();
      // For long text, insert in chunks to avoid browser limits
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
    } catch (e) {
      log(`execCommand failed: ${e.message}`);
    }

    // Strategy 2: Clipboard API paste
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
      } catch (e) {
        log(`Clipboard paste failed: ${e.message}`);
      }
    }

    // Strategy 3: Synthetic ClipboardEvent paste
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
      } catch (e) {
        log(`Synthetic paste failed: ${e.message}`);
      }
    }

    // Strategy 4: Direct innerHTML + InputEvent (last resort — may not enable send button)
    if (!success) {
      const escaped = text
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/\n/g, "<br>");
      input.innerHTML = `<p>${escaped}</p>`;
      input.dispatchEvent(new InputEvent("input", {
        bubbles: true, cancelable: true,
        inputType: "insertText", data: text,
      }));
      input.dispatchEvent(new Event("change", { bubbles: true }));
      await sleep(500);
      log("Prompt: set via innerHTML (last resort)");
      success = (input.textContent || "").length > 0;
    }

    // Force React/ProseMirror state sync: type a space then delete it.
    // This ensures ProseMirror processes at least one "real" input event,
    // which updates React state and enables the send button.
    if (success) {
      input.focus();
      // Move cursor to end
      const sel = window.getSelection();
      if (sel) {
        sel.selectAllChildren(input);
        sel.collapseToEnd();
      }
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

  // ── Click send ───────────────────────────────────────────────────────
  async function clickSend() {
    await sleep(1000); // Let UI catch up

    // Debug: log all buttons in the form area
    const debugBtns = [];
    const formEl = document.querySelector("form") || findPromptInput()?.closest("div[class]");
    if (formEl) {
      for (const btn of formEl.querySelectorAll("button")) {
        debugBtns.push({
          testid: btn.getAttribute("data-testid") || "",
          label: btn.getAttribute("aria-label") || "",
          disabled: btn.disabled,
          text: (btn.textContent || "").slice(0, 30),
          hasSvg: !!btn.querySelector("svg"),
        });
      }
    }
    log(`Send debug: ${debugBtns.length} buttons: ${JSON.stringify(debugBtns.slice(0, 5))}`);

    // Wait up to 60 seconds for send button to become enabled
    log("Waiting for send button to be ready...");
    for (let i = 0; i < 60; i++) {
      const btn = findSendButton();
      if (btn && !btn.disabled) {
        const tid = btn.getAttribute("data-testid");
        const lbl = btn.getAttribute("aria-label");
        log(`Send button found (testid=${tid}, label=${lbl}), clicking ONCE...`);
        btn.click();
        // Do NOT dispatch additional click events — after btn.click() the
        // send button morphs into stop-button. Any further click on the
        // same DOM element would STOP the generation.
        await sleep(500);
        return true;
      }

      // Every 5 iterations, try to wake up React by re-dispatching input events
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

    // Force-click: if send button exists but is disabled, force-enable and click
    const disabledSend = findSendButton(true); // allowDisabled=true
    if (disabledSend) {
      log(`Force-clicking disabled send button (testid=${disabledSend.getAttribute("data-testid")})`);
      disabledSend.disabled = false;
      disabledSend.removeAttribute("disabled");
      await sleep(100);
      disabledSend.click();
      // Single click only — no extra dispatches (same stop-button risk)
      await sleep(500);
      // Check if it worked (prompt cleared or stop button appeared)
      const inp = findPromptInput();
      const promptCleared = !inp || (inp.textContent || "").trim().length < 10;
      const stopBtn = document.querySelector("button[data-testid='stop-button']");
      if (promptCleared || stopBtn) {
        log("Force-click appears to have worked");
        return true;
      }
      log("Force-click may not have worked, trying Enter key...");
    }

    // Fallback 1: Enter key on prompt input
    const input = findPromptInput();
    if (input) {
      log("Send: trying Enter key...");
      input.focus();
      await sleep(100);

      // Dispatch a complete keyboard event chain
      for (const evtType of ["keydown", "keypress", "keyup"]) {
        input.dispatchEvent(new KeyboardEvent(evtType, {
          key: "Enter", code: "Enter", keyCode: 13, which: 13,
          bubbles: true, cancelable: true,
        }));
        await sleep(50);
      }
      await sleep(500);

      // Check if the prompt was cleared (indicating send worked)
      const remaining = (input.textContent || "").trim();
      if (remaining.length < 10) {
        log("Send: Enter key appears to have worked (prompt cleared)");
        return true;
      }
      log(`Send: Enter key may not have worked (${remaining.length} chars remain)`);
    }

    // Fallback 2: find ANY enabled button and click it (absolute last resort)
    if (formEl) {
      const lastResort = formEl.querySelector("button:not([disabled])");
      if (lastResort) {
        log(`Send: last resort click on button: ${lastResort.getAttribute("data-testid") || lastResort.textContent?.slice(0, 20)}`);
        lastResort.click();
        return true;
      }
    }

    log("ERROR: cannot send after 30s wait");
    return false;
  }

  // ── Wait for response to complete ────────────────────────────────────

  // The prompt text we sent — used to separate prompt from response
  let sentPromptText = "";
  // Set of text lines present AFTER clicking send (before response appears)
  // Any new lines that appear later = the response
  let postSendLines = new Set();

  function setSentPrompt(text) {
    sentPromptText = text;
  }

  function looksLikePromptEcho(text) {
    // Detect when extractResponseText returns the USER's message instead of
    // the assistant's response.  This must NOT flag legitimate reviews that
    // quote large portions of the paper — those are real responses.
    if (!sentPromptText || sentPromptText.length < 20) return false;
    const t = text.trim();
    // 1) Starts with user-message indicator → always a prompt echo
    if (/^(你说|You said)/i.test(t)) return true;
    // 2) Strip UI chrome and check prompt-prefix match.
    //    Only flag as echo if the text IS the prompt (same length), not if it
    //    merely starts with the prompt's opening.
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
    // 3) Very high overlap: only flag if text is essentially the prompt.
    //    A real review of a 40KB paper may quote 30-50% of it in citations,
    //    so 40% overlap is not enough. Require 80%+ overlap AND similar length.
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

  // Chrome/UI lines to always strip
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

  // SSR/hydration garbage patterns — page not fully rendered yet
  const SSR_GARBAGE_RE = /window\.__oai_log|window\.__oai_SSR|requestAnimationFrame/;

  function isChromeLine(t) {
    if (!t || t.length > 200) return false;
    return CHROME_RE.some(re => re.test(t));
  }

  function cleanText(text) {
    return text.split("\n").filter(line => {
      const t = line.trim();
      if (!t) return true;
      return !isChromeLine(t);
    }).join("\n").trim();
  }

  // Extract innerText from an element, but replace math renderings
  // (KaTeX, MathJax, MathML) with their LaTeX source. Without this,
  // rendered formulas get shattered into one-glyph-per-line garbage.
  function extractTextWithMath(el) {
    if (!el) return "";
    const clone = el.cloneNode(true);

    // Strategy 1: KaTeX — <annotation encoding="application/x-tex">LaTeX</annotation>
    // The .katex-mathml wrapper contains the annotation; replace the
    // enclosing .katex span with the LaTeX source.
    for (const ann of Array.from(
        clone.querySelectorAll('annotation[encoding="application/x-tex"]'))) {
      const latex = (ann.textContent || "").trim();
      if (!latex) continue;
      // Find the outer .katex container (display or inline)
      const katexOuter = ann.closest(".katex-display, .katex") || ann.parentElement;
      if (katexOuter) {
        const isDisplay = katexOuter.classList.contains("katex-display") ||
                          (katexOuter.parentElement &&
                           katexOuter.parentElement.classList.contains("katex-display"));
        const wrapped = isDisplay ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        katexOuter.replaceWith(document.createTextNode(wrapped));
      }
    }

    // Strategy 2: MathJax — <mjx-container> has child <math> with
    // semantics > annotation[encoding="TeX"] OR mjx-assistive-mml
    for (const mjx of Array.from(clone.querySelectorAll("mjx-container"))) {
      let latex = "";
      // 2a: look for MathML annotation
      const mmlAnn = mjx.querySelector('annotation[encoding*="TeX"]');
      if (mmlAnn) latex = (mmlAnn.textContent || "").trim();
      // 2b: aria-label fallback
      if (!latex) latex = mjx.getAttribute("aria-label") || "";
      // 2c: data attribute fallback
      if (!latex) latex = mjx.getAttribute("data-latex") || "";
      if (latex) {
        const isDisplay = mjx.getAttribute("display") === "true" ||
                          mjx.getAttribute("data-display") === "block";
        const wrapped = isDisplay ? `\n$$${latex}$$\n` : ` $${latex}$ `;
        mjx.replaceWith(document.createTextNode(wrapped));
      }
    }

    // Strategy 3: Generic [data-math-tex] or [data-tex] (some ChatGPT versions)
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

    // Strategy 4: Bare MathML (no KaTeX/MathJax wrapper) — fall back to
    // dropping rendered spans and using the MathML serialization if present
    for (const math of Array.from(clone.querySelectorAll("math"))) {
      // If already replaced above via annotation, skip
      if (!math.isConnected) continue;
      const alttext = math.getAttribute("alttext") || "";
      if (alttext) {
        math.replaceWith(document.createTextNode(` $${alttext}$ `));
      }
      // Otherwise leave the math element alone — innerText will use its
      // text content, which at least avoids the glyph-per-line issue
      // caused by KaTeX/MathJax rendered spans.
    }

    return (clone.innerText || "").trim();
  }

  function stripSSRGarbage(text) {
    // Remove SSR bootstrap script fragments from extracted text instead of
    // rejecting the entire response. Real ChatGPT replies can get mixed with
    // SSR remnants in the same DOM extraction pass.
    if (!text) return text;
    // Remove known SSR script patterns
    let cleaned = text
      .replace(/I?window\.__oai_logHTML\?[^)]*\)\s*/g, "")
      .replace(/window\.__oai_SSR_HTML\s*=\s*window\.__oai_SSR_HTML\s*\|\|\s*Date\.now\(\)\s*;?\s*/g, "")
      .replace(/requestAnimationFrame\(\(function\(\)\{[^}]*\}\)\)\s*/g, "")
      .replace(/window\.__oai_logTTI\?[^)]*\)\s*/g, "")
      .replace(/window\.__oai_SSR_TTI\s*=\s*window\.__oai_SSR_TTI\s*\|\|\s*Date\.now\(\)\s*;?\s*/g, "")
      .replace(/ChatGPT said:/g, "")
      .trim();
    return cleaned;
  }

  function isSSROnly(text) {
    // Returns true ONLY if the text is ENTIRELY SSR garbage with no real content.
    if (!text || text.length < 10) return false;
    const stripped = stripSSRGarbage(text);
    // After stripping SSR, filter chrome lines too
    const lines = stripped.split("\n").filter(l => {
      const t = l.trim();
      return t.length > 0 && !isChromeLine(t);
    });
    return lines.join("").trim().length < 20;
  }

  function extractResponseText() {
    // ═══ Strategy S0: Shadow DOM extraction (ChatGPT 5.4 Pro) ═══
    // ChatGPT 5.4 Pro renders conversation inside a shadow root.
    // Standard querySelector can't reach inside.
    // IMPORTANT: skip extraction if ChatGPT is still thinking/generating —
    // shadow root has thinking preamble text that looks like content but isn't.
    for (const el of document.querySelectorAll("*")) {
      if (!el.shadowRoot) continue;

      // Quick check: is this shadow root still in thinking state?
      const rawPreview = (el.shadowRoot.textContent || "").slice(0, 2000);
      if (/Pro thinking|Thought for \d|正在思考|I'm checking|I'm looking|I'm searching|I'm analyzing/i.test(rawPreview)) {
        // Check if there's ALSO a substantial response (thinking is done, response follows)
        if (rawPreview.length < 3000) continue;  // still thinking, skip
      }

      // Helper: get clean text from shadow element (skip style/script content)
      function shadowInnerText(root) {
        // Can't clone ShadowRoot — walk children and collect text, skipping style/script
        let text = "";
        function walk(node) {
          if (node.nodeType === Node.TEXT_NODE) {
            text += node.textContent;
            return;
          }
          if (node.nodeType !== Node.ELEMENT_NODE) return;
          const tag = node.tagName?.toLowerCase();
          if (tag === "style" || tag === "script" || tag === "link") return;
          for (const child of node.childNodes) walk(child);
          // Add newline after block elements
          if (/^(div|p|h[1-6]|li|br|article|section|blockquote|pre|tr)$/.test(tag)) {
            text += "\n";
          }
        }
        if (root.childNodes) {
          for (const child of root.childNodes) walk(child);
        }
        return text.trim();
      }

      // Find assistant messages inside shadow DOM
      const assistantEls = el.shadowRoot.querySelectorAll(
        "[data-message-author-role='assistant'], " +
        "div[class*='markdown'], div[class*='prose'], " +
        "article, [class*='agent-turn']"
      );
      if (assistantEls.length > 0) {
        // Take the last (most recent) assistant message
        const lastAssistant = assistantEls[assistantEls.length - 1];
        const text = cleanText(shadowInnerText(lastAssistant));
        if (text.length > 100 && !looksLikePromptEcho(text)) {
          return text;
        }
      }

      // Helper: strip ChatGPT thinking preamble from extracted text
      function stripThinkingPreamble(t) {
        return t
          .replace(/^ChatGPT said:\s*/i, "")
          .replace(/^I'm (?:checking|looking|searching|thinking|analyzing)[^.]*\.\s*/i, "")
          .replace(/^Thought for \d+[sm]\s*\d*[sm]?\s*/i, "")
          .trim();
      }

      // Fallback: get all text from shadow, stripped of CSS/JS
      const shadowText = shadowInnerText(el.shadowRoot);
      if (shadowText.length < 500) continue;

      // Try tail-anchor split
      if (sentPromptText.length > 50) {
        const tail = sentPromptText.slice(-80).trim();
        const idx = shadowText.lastIndexOf(tail);
        if (idx >= 0) {
          const after = stripThinkingPreamble(cleanText(shadowText.slice(idx + tail.length)));
          if (after.length > 100) return after;
        }
      }

      // Last resort: take second 60% (prompt first, response second)
      const halfPoint = Math.floor(shadowText.length * 0.4);
      const secondHalf = stripThinkingPreamble(cleanText(shadowText.slice(halfPoint)));
      if (secondHalf.length > 200 && !looksLikePromptEcho(secondHalf)) {
        return secondHalf;
      }
    }

    const main = document.querySelector("main");
    if (!main) return "";

    // Use math-aware extraction so KaTeX/MathJax formulas become $..$ or $$..$$
    const fullText = extractTextWithMath(main);

    // ═══ Strategy A1: Page-minus-prompt (tail-anchor) ═══
    // For long prompts (papers, code), use the LAST 100 chars of the prompt
    // as an anchor — unique enough to not recur inside the response.
    // Take everything after the anchor as the response. This is the most
    // reliable strategy for paper reviews where the response references
    // many passages from the prompt.
    if (sentPromptText.length > 500) {
      const tailAnchor = sentPromptText.slice(-100).trim();
      let idx = fullText.lastIndexOf(tailAnchor);
      if (idx < 0 && tailAnchor.length > 50) {
        idx = fullText.lastIndexOf(tailAnchor.slice(-50));
      }
      if (idx >= 0) {
        const after = cleanText(fullText.slice(idx + tailAnchor.length));
        if (after.length > 100) {
          return after;
        }
      }
    }

    // ═══ Strategy A2: "Biggest non-prompt text block" ═══
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

      // Skip full-page candidate if smaller candidates exist
      const pageLen = fullText.length;
      if (cleaned.length > pageLen * 0.95 && candidates.length > 3) continue;

      if (looksLikePromptEcho(cleaned)) continue;

      // Strict prompt-prefix rejection: only reject if candidate IS the
      // prompt (length within 1.1x), not just quotes it.
      if (sentPromptText.length > 500) {
        const promptStart = sentPromptText.slice(0, 200).trim();
        if (cleaned.startsWith(promptStart)
            && cleaned.length <= sentPromptText.length * 1.1) {
          continue;
        }
      }

      return cleaned;
    }

    // ═══ Strategy B: Selector-based (legacy, still useful as fallback) ═══
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

    // ═══ Strategy C: Full-page text minus prompt (absolute fallback) ═══
    // fullText already declared at top of function; just re-check length
    if (fullText.length < 100) return "";

    // Try to locate prompt in page text and take everything after it
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

    // Strategy D: Line-diff against post-send snapshot
    if (postSendLines.size > 0) {
      const newLines = fullText.split("\n").filter(l => {
        const t = l.trim();
        return t.length > 0 && !postSendLines.has(t) && !isChromeLine(t);
      });
      if (newLines.length > 3) {
        const diffText = newLines.join("\n").trim();
        if (diffText.length > 100 && !looksLikePromptEcho(diffText)) {
          return diffText;
        }
      }
    }

    return "";
  }

  function getDepth(el) {
    let depth = 0;
    let node = el;
    while (node.parentElement) { depth++; node = node.parentElement; }
    return depth;
  }

  function cleanChromeLines(text) {
    const lines = text.split("\n");
    const cleaned = lines.filter(line => {
      const t = line.trim();
      if (!t) return true;
      // Remove known chrome
      if (/^(进阶专业|ChatGPT\s*也可能会犯错|请核查重要信息|查看\s*Cookie|Cookie\s*首选项)/.test(t)) return false;
      if (/^(ChatGPT can make mistakes|Check important info)/.test(t)) return false;
      if (/^Thought for \d+/.test(t)) return false;
      if (/^(你说|You said|ChatGPT\s*说|ChatGPT\s*said)[：:]?\s*$/.test(t)) return false;
      if (/^(正在思考|正在搜索|Searching)/.test(t)) return false;
      // Remove PDF filename line and bare "main" artifacts
      if (/^main(\.pdf)?\s*$/.test(t)) return false;
      if (/^PDF\s*$/.test(t)) return false;
      // Remove nav/sidebar artifacts
      if (/^(新建聊天|New chat|ChatGPT|GPT-4|GPT-5|升级|Upgrade|Log out|登出)\s*$/.test(t)) return false;
      return true;
    }).join("\n").trim();
    return cleaned;
  }

  function isStillGenerating() {
    // Check light DOM first
    if (
      document.querySelector("button[aria-label='Stop generating']") ||
      document.querySelector("button[aria-label='Stop streaming']") ||
      document.querySelector("button[aria-label='停止生成']") ||
      document.querySelector("button[aria-label='停止流式传输']") ||
      document.querySelector("button[data-testid='stop-button']") ||
      document.querySelector("[class*='result-streaming']") ||
      document.querySelector("[class*='streaming']") ||
      document.querySelector("[class*='thinking']") ||
      document.querySelector("[class*='progress']")
    ) return true;

    // Check inside Shadow DOM (ChatGPT 5.4 Pro renders there)
    for (const el of document.querySelectorAll("*")) {
      if (!el.shadowRoot) continue;
      if (
        el.shadowRoot.querySelector("button[aria-label='Stop generating']") ||
        el.shadowRoot.querySelector("button[aria-label='Stop streaming']") ||
        el.shadowRoot.querySelector("button[data-testid='stop-button']") ||
        el.shadowRoot.querySelector("[class*='streaming']") ||
        el.shadowRoot.querySelector("[class*='thinking']") ||
        el.shadowRoot.querySelector("[class*='progress']")
      ) return true;
      // Also check for "Pro thinking" text in shadow DOM
      const text = (el.shadowRoot.textContent || "").slice(0, 2000);
      if (/Pro thinking|Thought for \d|正在思考|Searching|Deep research/i.test(text)
          && text.length < 3000) return true;
    }
    return false;
  }

  async function waitForResponse(task_id, minResponseLength = DEFAULT_MIN_RESPONSE_LENGTH) {
    log("Waiting for ChatGPT response...");

    const startTime = Date.now();
    let lastText = "";
    let stableCount = 0;
    let lastLogTime = 0;
    let lastHeartbeat = 0;

    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);

      let responseText = extractResponseText();
      const generating = isStillGenerating();
      const elapsed = Math.floor((Date.now() - startTime) / 1000);
      const mainLen = (document.querySelector("main")?.innerText || "").length;

      if (Date.now() - lastHeartbeat >= 60000) {
        lastHeartbeat = Date.now();
        const phase = generating ? "waiting_response" : "response_observed";
        const detail = `elapsed=${elapsed}s; extracted=${responseText.length}; page=${mainLen}; stable=${stableCount}; gen=${generating}`;
        try { await postPhase(task_id, phase, detail); } catch {}
      }

      // Periodic status log (every 2 min)
      if (elapsed - lastLogTime >= 120) {
        lastLogTime = elapsed;
        log(`Wait: ${elapsed}s, extracted=${responseText.length}, page=${mainLen}, stable=${stableCount}, gen=${generating}, url=${window.location.href.slice(-30)}`);
        // DOM debug: comprehensive search for where content lives
        const dbg = [];
        for (const s of ["main", "[data-message-author-role]", "[data-message-author-role='assistant']", "article", "[data-testid*='conversation-turn']", "div[class*='markdown']", "div[class*='prose']", "[class*='agent-turn']", "[role='presentation']", "[class*='conversation']", "[class*='thread']"]) {
          const els = document.querySelectorAll(s);
          if (els.length > 0) {
            const maxLen = Math.max(...Array.from(els).map(e => (e.innerText||"").length));
            dbg.push(`${s}:${els.length}(max=${maxLen})`);
          }
        }
        log(`DOM debug: ${dbg.join(", ") || "NO MATCHES"}`);

        // Deep scan: check shadow DOM, iframes, and all large text nodes
        let shadowCount = 0, iframeCount = 0, biggestText = 0;
        document.querySelectorAll("*").forEach(el => {
          if (el.shadowRoot) {
            shadowCount++;
            const sText = (el.shadowRoot.textContent || "").length;
            if (sText > biggestText) biggestText = sText;
          }
        });
        const iframes = document.querySelectorAll("iframe");
        iframeCount = iframes.length;
        let iframeBiggest = 0;
        iframes.forEach(f => {
          try {
            const len = (f.contentDocument?.body?.innerText || "").length;
            if (len > iframeBiggest) iframeBiggest = len;
          } catch(e) { /* cross-origin */ }
        });

        // Check body total text vs main text
        const bodyLen = (document.body?.innerText || "").length;

        // Find the single biggest div by innerText
        let bigDiv = 0, bigDivTag = "";
        document.querySelectorAll("div").forEach(d => {
          const len = (d.innerText || "").length;
          if (len > bigDiv) {
            bigDiv = len;
            bigDivTag = d.className?.slice(0, 50) || d.id || "anon";
          }
        });

        log(`DEEP: body=${bodyLen}, biggestDiv=${bigDiv}(${bigDivTag}), shadows=${shadowCount}(max=${biggestText}), iframes=${iframeCount}(max=${iframeBiggest})`);
      }

      // Only count extracted text that's meaningful
      if (responseText.length >= 5) {
        // HARD GATE: ignore UI chrome, thinking preambles, footers, and
        // transition fragments before stability counting.
        if (responseText.length < minResponseLength) {
          if (stableCount === 0) {
            log(`Too short (${responseText.length} < ${minResponseLength} chars) - waiting for complete response`);
          }
          stableCount = 0;
          lastText = "";
          continue;
        }

        // CRITICAL: never accept a prompt echo as a response.
        if (looksLikePromptEcho(responseText)) {
          if (stableCount === 0) {
            log(`Prompt echo detected (${responseText.length} chars) — waiting for real response`);
          }
          stableCount = 0;
          lastText = "";
          continue;
        }

        // Strip SSR/hydration fragments from response (they can mix with real text)
        if (SSR_GARBAGE_RE.test(responseText)) {
          responseText = stripSSRGarbage(responseText);
          // If NOTHING remains after stripping, page is still hydrating
          if (isSSROnly(responseText)) {
            if (stableCount === 0) {
              log(`SSR-only content (${responseText.length} chars) — page still hydrating, waiting`);
            }
            stableCount = 0;
            lastText = "";
            continue;
          }
          log(`Stripped SSR fragments, ${responseText.length} chars remain`);
        }

        if (responseText === lastText) {
          stableCount++;
          // Determine minimum stability checks based on response size.
          // Large responses (>=2000 chars) are almost certainly real — 3 checks.
          // Medium (200-2000) — 5 checks (guard against thinking preamble).
          // Tiny (<200) — 9 checks (likely UI chrome, wait longer).
          let minChecks;
          if (responseText.length >= 2000) {
            minChecks = STABLE_CHECKS;        // 3
          } else if (responseText.length >= 200) {
            minChecks = STABLE_CHECKS + 2;    // 5
          } else {
            minChecks = STABLE_CHECKS * 3;    // 9
          }

          const stableEnough = stableCount >= minChecks && !generating;
          // Override: if stable for very long regardless of gen flag
          // (ChatGPT 5.4 sometimes keeps stale [class*='thinking'])
          const stableOverride = stableCount >= minChecks + 3;
          if (stableEnough || stableOverride) {
            log(`Response complete: ${responseText.length} chars (stable ${stableCount * STABLE_INTERVAL / 1000}s, gen=${generating})`);
            return responseText;
          }

          // Log progress for short responses
          if (responseText.length < 2000 && stableCount % 3 === 0) {
            log(`Short response (${responseText.length} chars) - waiting for stable completion (${elapsed}s)`);
          }
        } else {
          stableCount = 0;
          lastText = responseText;
        }
      } else if (generating) {
        // Still generating but no extracted text yet — keep waiting
        stableCount = 0;
      }
    }

    log(`TIMEOUT (${MAX_WAIT/1000}s), returning partial: ${lastText.length} chars`);
    return lastText;
  }

  // ── Process a task ───────────────────────────────────────────────────
  async function processTask(task) {
    const { task_id, prompt, pdf_base64, pdf_name, min_response_length } = task;
    const minResponseLength = Number.isFinite(Number(min_response_length))
      ? Number(min_response_length)
      : DEFAULT_MIN_RESPONSE_LENGTH;
    log(`=== Task: ${task_id} ===`);
    busy = true;
    updatePanel();

    try {
      if (!isForegroundReady()) {
        await releaseTask(task_id, `tab_not_foreground (${foregroundState()})`);
        return;
      }
      await postPhase(task_id, "foreground_claimed", foregroundState());

      // Navigate to a fresh chat page if we're not already on one.
      // IMPORTANT: Only redirect if we're actively processing a task.
      // Never hijack the user's normal ChatGPT browsing.
      if (!isOnNewChatPage()) {
        // Mark that WE are about to navigate (not the user)
        GM_setValue(GM_KEY("oracle_navigating"), true);
        GM_setValue(GM_KEY("nav_task_id"), task_id);
        setTaskPhase("navigating");
        const agentNum = AGENT_ID.replace("oracle_", "");
        log(`Not on fresh chat — navigating to chatgpt.com ...`);
        busy = false;
        updatePanel();
        window.location.href = `https://chatgpt.com/?oracle=${agentNum}`;
        return; // Script re-inits on new page, resumes from init()
      }

      // ACK the task (only after we're on the right page)
      try { await serverPost("/ack", { task_id, agent_id: AGENT_ID, phase: "page_ready" }); } catch {}

      setTaskPhase("processing");

      // Wait for prompt input to appear
      let retries = 0;
      while (!findPromptInput() && retries < 60) {
        if (retries > 0 && retries % 10 === 0) {
          await postPhase(task_id, "waiting_prompt_input", foregroundState());
        }
        await sleep(1000);
        retries++;
      }
      if (!findPromptInput()) {
        throw new Error("Prompt input not found after 60s wait");
      }
      log("Page ready");
      if (!isForegroundReady()) {
        await releaseTask(task_id, `lost_foreground_before_prompt (${foregroundState()})`);
        return;
      }
      await postPhase(task_id, "prompt_ready", foregroundState());

      // Upload PDF if present
      if (pdf_base64) {
        await uploadPDF(pdf_base64, pdf_name || "paper.pdf");
        // Extra wait after upload — ensure ChatGPT fully processes the file
        log("Waiting 15s for PDF to be fully processed...");
        await sleep(15000);
      }

      // Enter prompt
      const entered = await enterPrompt(prompt);
      if (!entered) {
        throw new Error("Failed to enter prompt text");
      }

      // Store prompt text for response extraction
      setSentPrompt(prompt);
      await postPhase(task_id, "prompt_inserted", `chars=${prompt.length}; ${foregroundState()}`);

      // Wait for send button to become enabled (upload + text both ready)
      log("Waiting for send button to enable...");
      let sendReady = false;
      for (let i = 0; i < 30; i++) {  // up to 30s
        const btn = findSendButton();
        if (btn && !btn.disabled) {
          sendReady = true;
          log(`Send button enabled after ${i}s`);
          break;
        }
        await sleep(1000);
      }
      if (!sendReady) {
        log("WARNING: send button still disabled after 30s, will try force-click");
      }

      // Send
      const urlBefore = window.location.href;
      const sent = await clickSend();
      if (!sent) {
        throw new Error("Failed to click send");
      }
      await postPhase(task_id, "sent", foregroundState());

      // Wait for URL change — ChatGPT redirects from chatgpt.com to
      // chatgpt.com/c/{id} after accepting a message. This is critical:
      // the entire DOM changes during this SPA navigation.
      log(`Sent. Waiting for URL change (was: ${urlBefore.slice(-30)})...`);
      let urlChanged = false;
      for (let i = 0; i < 60; i++) {  // up to 60s
        await sleep(1000);
        if (window.location.href !== urlBefore) {
          urlChanged = true;
          log(`URL changed to: ${window.location.href.slice(-40)}`);
          break;
        }
        // Also check if response already started (same-page conversation)
        if (isStillGenerating()) {
          log("Response generation detected (same page)");
          break;
        }
      }
      if (!urlChanged && !isStillGenerating()) {
        log("WARNING: URL did not change and no generation detected after 60s");
      }

      // Wait for new page DOM to settle after SPA navigation
      await sleep(5000);

      // Capture page state NOW (on the conversation page, not homepage)
      capturePostSendState();
      await postPhase(task_id, "waiting_response", `url=${window.location.href.slice(-80)}`);
      const response = await waitForResponse(task_id, minResponseLength);

      if (!response || response.length < 5) {
        throw new Error(`Response too short or empty (${response?.length || 0} chars)`);
      }

      // Post result
      await serverPost("/result", {
        task_id,
        response,
        model: task.model || "unknown",
        agent_id: AGENT_ID,
      });

      log(`DONE: ${task_id} (${response.length} chars)`);
      clearTaskState();
    } catch (err) {
      log(`ERROR: ${err.message}`);
      try {
        await serverPost("/result", {
          task_id,
          response: `ERROR: ${err.message}`,
          model: task.model || "unknown",
          agent_id: AGENT_ID,
        });
      } catch {}
      clearTaskState();
    } finally {
      busy = false;
      updatePanel();
    }
  }

  // ── Main loop ────────────────────────────────────────────────────────
  async function pollLoop() {
    while (true) {
      // Re-read active state each iteration (user may toggle mid-loop)
      active = GM_getValue(GM_KEY("oracle_active"), true);
      if (active && !busy) {
        try {
          if (!isForegroundReady()) {
            if (logHistory.length === 0 || !logHistory[logHistory.length - 1].includes("waiting for foreground")) {
              log(`ACTIVE but waiting for foreground before polling (${foregroundState()})`);
            }
            await sleep(POLL_INTERVAL);
            continue;
          }
          const task = await serverGet(`/task?agent=${AGENT_ID}`);
          if (task && task.task_id && task.status !== "idle") {
            // Double-check active right before processing
            if (!GM_getValue(GM_KEY("oracle_active"), true)) {
              log("Task available but oracle is PAUSED — skipping");
            } else {
              await processTask(task);
            }
          }
        } catch (err) {
          // Server offline — silently continue
          if (logHistory.length === 0 || !logHistory[logHistory.length-1].includes("unreachable")) {
            log(`Server unreachable`);
          }
        }
      }
      await sleep(POLL_INTERVAL);
    }
  }

  // ── Bootstrap ────────────────────────────────────────────────────────
  async function init() {
    const agentLabel = AGENT_ID.replace("oracle_", "#");
    log(`Oracle Bridge v${SCRIPT_VERSION} agent ${agentLabel} — ${active ? "ACTIVE" : "PAUSED"}`);

    // Check if WE navigated here (not the user clicking around)
    const phase = getTaskPhase();
    const navTaskId = GM_getValue(GM_KEY("nav_task_id"), "");
    const oracleNav = GM_getValue(GM_KEY("oracle_navigating"), false);
    const urlHasOracleFlag = /[?&]oracle=\d/.test(window.location.search);

    // Only resume task processing if this navigation was initiated by this agent
    if (phase === "navigating" && navTaskId && (oracleNav || urlHasOracleFlag)) {
      log(`Resuming after navigation for task: ${navTaskId}`);
      GM_setValue(GM_KEY("nav_task_id"), "");
      GM_setValue(GM_KEY("oracle_navigating"), false);
      clearTaskState();

      // Clean oracle flag from URL without triggering navigation
      if (urlHasOracleFlag) {
        const cleanUrl = window.location.href.replace(/[?&]oracle=\d+/, "").replace(/\?$/, "");
        history.replaceState(null, "", cleanUrl);
      }

      await sleep(3000); // Let fresh chat page fully load

      // Re-fetch this agent's pending task from the server
      try {
        const task = await serverGet(`/task?agent=${AGENT_ID}`);
        if (task && task.task_id && task.status !== "idle") {
          log(`Re-fetched task: ${task.task_id} (prompt ${task.prompt?.length || 0} chars, pdf=${!!task.pdf_base64})`);
          await processTask(task);
        } else {
          log("WARNING: server returned no pending task after navigation");
        }
      } catch (e) {
        log(`Failed to re-fetch task after navigation: ${e.message}`);
      }
    } else if (phase === "navigating") {
      // Stale navigating state — clear it
      log("Clearing stale navigation state");
      GM_setValue(GM_KEY("nav_task_id"), "");
      GM_setValue(GM_KEY("oracle_navigating"), false);
      clearTaskState();
    }

    // Start polling
    pollLoop();
  }

  // Run after page is fully loaded (script runs at document-start,
  // so DOM/body won't exist yet — defer everything to load event)
  function startWhenReady() {
    if (document.readyState === "complete") {
      setTimeout(init, 2000);
    } else {
      window.addEventListener("load", () => setTimeout(init, 2000));
    }
  }
  startWhenReady();
})();
