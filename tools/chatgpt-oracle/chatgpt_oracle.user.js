// ==UserScript==
// @name         ChatGPT Oracle Bridge
// @namespace    omega-automath
// @version      2.6
// @description  Bridges local oracle_server.py with ChatGPT Pro for automated paper review
// @match        https://chatgpt.com/*
// @match        https://chat.openai.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @connect      localhost
// @connect      127.0.0.1
// @run-at       document-idle
// ==/UserScript==

(function () {
  "use strict";

  const SERVER = "http://localhost:8765";
  const POLL_INTERVAL = 5000;
  const STABLE_CHECKS = 5;       // response must be stable for 5 checks
  const STABLE_INTERVAL = 4000;   // check every 4 seconds
  const MAX_WAIT = 1800000;       // 30 minutes

  let busy = false;

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
    const lines = logHistory.slice(-10).map(l => `<div>${l}</div>`).join("");
    panel.innerHTML = `<b>[Oracle Bridge v2.6]</b> ${busy ? "BUSY" : "idle"}<hr style="border-color:#333;margin:4px 0">${lines}`;
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

  function sleep(ms) {
    return new Promise((r) => setTimeout(r, ms));
  }

  // ── Persistent task state (survives page navigation) ─────────────────
  function saveTaskState(task) {
    GM_setValue("current_task", JSON.stringify(task));
    GM_setValue("task_phase", "pending");
  }
  function loadTaskState() {
    try {
      const s = GM_getValue("current_task", "");
      return s ? JSON.parse(s) : null;
    } catch { return null; }
  }
  function getTaskPhase() {
    return GM_getValue("task_phase", "");
  }
  function setTaskPhase(phase) {
    GM_setValue("task_phase", phase);
  }
  function clearTaskState() {
    GM_setValue("current_task", "");
    GM_setValue("task_phase", "");
  }

  // ── DOM helpers for ChatGPT UI ───────────────────────────────────────

  function findPromptInput() {
    // ChatGPT 2024-2025 uses ProseMirror contenteditable div
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

  function findSendButton() {
    // Layer 1: Exact data-testid / aria-label selectors (updated 2025-2026)
    for (const sel of [
      "button[data-testid='send-button']",
      "button[data-testid='composer-send-button']",
      "button[data-testid='send-button']:not([disabled])",
      "button[aria-label='Send prompt']",
      "button[aria-label='Send']",
      "button[aria-label='Send message']",
      "button[aria-label='Submit']",
    ]) {
      const el = document.querySelector(sel);
      if (el && !el.disabled) return el;
    }

    // Layer 2: Find by partial data-testid containing "send"
    for (const btn of document.querySelectorAll("button[data-testid]")) {
      const tid = btn.getAttribute("data-testid") || "";
      if (tid.toLowerCase().includes("send") && !btn.disabled) return btn;
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
        const svg = btn.querySelector("svg");
        if (svg) {
          // Send buttons typically have a polyline/path pointing upward or an arrow
          const paths = svg.querySelectorAll("path, polyline, line");
          if (paths.length > 0 && paths.length < 5) {
            // Likely a simple icon button (not a complex menu icon)
            // Check it's near the input area (bottom of composer)
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
          // Skip buttons that look like they're for other purposes
          const label = (btn.getAttribute("aria-label") || btn.textContent || "").toLowerCase();
          if (label.includes("attach") || label.includes("file") || label.includes("mic") ||
              label.includes("voice") || label.includes("new") || label.includes("model")) continue;
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
    // New chat page has no conversation messages
    const msgs = document.querySelectorAll("[data-message-author-role]");
    return msgs.length === 0;
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
    await sleep(200);

    // Strategy 1: Write to clipboard and paste (most reliable for ProseMirror)
    let success = false;
    try {
      await navigator.clipboard.writeText(text);
      document.execCommand("paste");
      await sleep(500);
      if ((input.textContent || "").length > 10) {
        success = true;
        log("Prompt: pasted via clipboard API");
      }
    } catch (e) {
      log(`Clipboard paste failed: ${e.message}`);
    }

    // Strategy 2: Synthetic ClipboardEvent paste
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

    // Strategy 3: execCommand insertText
    if (!success) {
      try {
        input.focus();
        input.innerHTML = "";
        document.execCommand("selectAll", false, null);
        document.execCommand("insertText", false, text);
        await sleep(500);
        if ((input.textContent || "").length > 10) {
          success = true;
          log("Prompt: inserted via execCommand");
        }
      } catch (e) {
        log(`execCommand failed: ${e.message}`);
      }
    }

    // Strategy 4: Direct innerHTML + InputEvent (last resort)
    if (!success) {
      const escaped = text
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/\n/g, "<br>");
      input.innerHTML = `<p>${escaped}</p>`;
      // Fire InputEvent which React/ProseMirror actually listens to
      input.dispatchEvent(new InputEvent("input", {
        bubbles: true, cancelable: true,
        inputType: "insertText", data: text,
      }));
      input.dispatchEvent(new Event("change", { bubbles: true }));
      await sleep(500);
      log("Prompt: set via innerHTML (last resort)");
      success = (input.textContent || "").length > 0;
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

    // Wait up to 30 seconds for send button to become enabled
    log("Waiting for send button to be ready...");
    for (let i = 0; i < 60; i++) {
      const btn = findSendButton();
      if (btn && !btn.disabled) {
        // Try multiple click strategies
        btn.click();
        await sleep(200);

        // Also try MouseEvent dispatch (some React UIs need this)
        btn.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true }));
        await sleep(200);

        // Also try pointerdown/pointerup (modern event chain)
        btn.dispatchEvent(new PointerEvent("pointerdown", { bubbles: true }));
        btn.dispatchEvent(new PointerEvent("pointerup", { bubbles: true }));

        log(`Send button clicked (testid=${btn.getAttribute("data-testid")}, label=${btn.getAttribute("aria-label")})`);
        return true;
      }
      if (i > 0 && i % 10 === 0) {
        log(`Send button not ready yet... ${i * 0.5}s`);
      }
      await sleep(500);
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

  // The prompt text we sent — used as anchor to find the response
  let sentPromptText = "";
  // Page text captured right AFTER clicking send (before response appears)
  let postSendSnapshot = "";

  function setSentPrompt(text) {
    sentPromptText = text;
  }

  async function takePostSendSnapshot() {
    // Wait a moment for the UI to update with the sent message
    await sleep(3000);
    const main = document.querySelector("main");
    postSendSnapshot = main ? (main.innerText || "").trim() : "";
    log(`Post-send snapshot: ${postSendSnapshot.length} chars`);
  }

  // Known UI chrome strings to strip from extracted text
  const CHROME_STRINGS = [
    "进阶专业", "ChatGPT 也可能会犯错", "请核查重要信息", "查看 Cookie 首选项",
    "ChatGPT can make mistakes", "Check important info", "Cookie preferences",
    "Thought for", "正在思考", "正在搜索",
  ];

  function cleanChrome(text) {
    let cleaned = text;
    // Remove lines that are pure chrome
    const lines = cleaned.split("\n");
    const filtered = lines.filter(line => {
      const trimmed = line.trim();
      if (!trimmed) return true; // keep empty lines
      for (const chrome of CHROME_STRINGS) {
        if (trimmed.includes(chrome) && trimmed.length < chrome.length + 30) return false;
      }
      // Remove "Thought for Ns" lines
      if (/^Thought for \d+s?$/.test(trimmed)) return false;
      // Remove "你说：" / "ChatGPT 说：" headers
      if (/^(你说|You said|ChatGPT\s*说|ChatGPT\s*said)[：:]?\s*$/.test(trimmed)) return false;
      return true;
    });
    return filtered.join("\n").trim();
  }

  function extractResponseText() {
    const main = document.querySelector("main");
    if (!main) return "";
    const currentText = (main.innerText || "").trim();

    // ═══ STRATEGY 1: Prompt-anchor method ═══
    // Find our prompt text in the page, take everything AFTER it as the response
    if (sentPromptText.length > 20) {
      // Use a distinctive chunk of the prompt (first 80 chars) as anchor
      const anchor = sentPromptText.slice(0, 80).trim();
      const anchorIdx = currentText.indexOf(anchor);

      if (anchorIdx >= 0) {
        // Find the end of the full prompt in the page text
        // The prompt might be displayed with minor formatting changes,
        // so search for the end of the prompt block
        const promptEnd = anchorIdx + sentPromptText.length;

        // Try exact end first
        let afterPrompt = currentText.slice(promptEnd).trim();

        // If exact end didn't work well, try finding a longer anchor
        if (afterPrompt.length < 10 && sentPromptText.length > 100) {
          const longerAnchor = sentPromptText.slice(-60).trim();
          const longerIdx = currentText.indexOf(longerAnchor, anchorIdx);
          if (longerIdx >= 0) {
            afterPrompt = currentText.slice(longerIdx + longerAnchor.length).trim();
          }
        }

        if (afterPrompt.length > 0) {
          const cleaned = cleanChrome(afterPrompt);
          if (cleaned.length > 5) {
            return cleaned;
          }
        }
      }
    }

    // ═══ STRATEGY 2: Post-send diff ═══
    // Compare current text against snapshot taken right after send (before response)
    if (postSendSnapshot.length > 0 && currentText.length > postSendSnapshot.length + 10) {
      // The new text is the difference
      // Try to find where the old snapshot ends in the current text
      const snipLen = Math.min(postSendSnapshot.length, 300);
      const snip = postSendSnapshot.slice(0, snipLen);
      const idx = currentText.indexOf(snip);
      if (idx >= 0) {
        const afterOld = currentText.slice(idx + postSendSnapshot.length).trim();
        const cleaned = cleanChrome(afterOld);
        if (cleaned.length > 5) {
          return cleaned;
        }
      }

      // Alternative: just take the text growth
      const growth = currentText.slice(postSendSnapshot.length).trim();
      const cleanedGrowth = cleanChrome(growth);
      if (cleanedGrowth.length > 20) {
        return cleanedGrowth;
      }
    }

    // ═══ STRATEGY 3: Selector-based (classic & modern ChatGPT) ═══
    function lastText(sel) {
      try {
        const els = document.querySelectorAll(sel);
        if (els.length > 0) {
          return (els[els.length - 1].innerText || els[els.length - 1].textContent || "").trim();
        }
      } catch (e) {}
      return "";
    }

    function isNoise(text) {
      if (!text || text.length < 10) return true;
      for (const chrome of CHROME_STRINGS) {
        if (text.includes(chrome) && text.length < 200) return true;
      }
      if (text.includes(sentPromptText.slice(0, 40))) return true;
      return false;
    }

    let best = "";
    for (const sel of [
      "[data-message-author-role='assistant'] .markdown",
      "[data-message-author-role='assistant']",
      "article[data-testid*='assistant'] .markdown",
      "article[data-testid*='assistant']",
      "[data-testid*='conversation-turn']:last-child .markdown",
      ".agent-turn .markdown",
      "div[class*='markdown'][class*='prose']",
      "div[class*='markdown']",
      "div.prose",
    ]) {
      const t = lastText(sel);
      if (t.length > best.length && !isNoise(t)) best = t;
    }

    return best;
  }

  function isStillGenerating() {
    return !!(
      document.querySelector("button[aria-label='Stop generating']") ||
      document.querySelector("button[aria-label='Stop streaming']") ||
      document.querySelector("button[aria-label='停止生成']") ||
      document.querySelector("button[aria-label='停止流式传输']") ||
      document.querySelector("button[data-testid='stop-button']") ||
      document.querySelector("[class*='result-streaming']") ||
      document.querySelector("[class*='streaming']") ||
      document.querySelector("[class*='thinking']") ||
      document.querySelector("[class*='progress']")
    );
  }

  async function waitForResponse() {
    log("Waiting for ChatGPT response...");

    const startTime = Date.now();
    let lastText = "";
    let stableCount = 0;
    let lastLogTime = 0;
    let debugCount = 0;

    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);

      const responseText = extractResponseText();
      const elapsed = Math.floor((Date.now() - startTime) / 1000);

      // Debug: log DOM state periodically (first 3 times)
      if (debugCount < 3 && elapsed > 8 * (debugCount + 1)) {
        debugCount++;
        const counts = {};
        for (const sel of [
          "[data-message-author-role='assistant']",
          "[data-message-author-role='user']",
          "article[data-testid*='assistant']",
          "div[class*='markdown']",
          "div.prose",
          "[class*='streaming']",
          "[class*='result-streaming']",
          "[data-testid*='conversation-turn']",
        ]) {
          try { counts[sel] = document.querySelectorAll(sel).length; } catch { counts[sel] = -1; }
        }
        log(`DOM debug #${debugCount}: ${JSON.stringify(counts)}, text=${responseText.length}`);

        // Deep probe: find all elements with data-testid in main area
        if (debugCount === 1) {
          try {
            const testids = new Set();
            document.querySelectorAll("main [data-testid]").forEach(el => {
              testids.add(el.getAttribute("data-testid"));
            });
            log(`DOM testids in main: ${JSON.stringify([...testids].slice(0, 15))}`);
          } catch (e) {}

          // Find elements with data-message-* attributes
          try {
            const msgAttrs = new Set();
            document.querySelectorAll("main [data-message-id], main [data-message-author-role]").forEach(el => {
              const role = el.getAttribute("data-message-author-role") || "";
              const tag = el.tagName;
              msgAttrs.add(`${tag}[role=${role}]`);
            });
            log(`DOM msg elements: ${JSON.stringify([...msgAttrs])}`);
          } catch (e) {}

          // Find the largest text blocks in main (top 3) with their tag info
          try {
            const blocks = [];
            document.querySelectorAll("main div, main article, main section").forEach(div => {
              const text = (div.innerText || "").trim();
              if (text.length > 30) {
                blocks.push({
                  len: text.length,
                  tag: div.tagName,
                  cls: (div.className || "").toString().slice(0, 50),
                  testid: div.getAttribute("data-testid") || "",
                  role: div.getAttribute("data-message-author-role") || "",
                  preview: text.slice(0, 40),
                });
              }
            });
            blocks.sort((a, b) => b.len - a.len);
            for (const b of blocks.slice(0, 3)) {
              log(`DOM block: len=${b.len} tag=${b.tag} cls="${b.cls}" testid="${b.testid}" role="${b.role}" "${b.preview}..."`);
            }
          } catch (e) {}
        }
      }

      // Only count text that's meaningful (not empty or too short)
      if (responseText.length >= 5) {
        if (responseText === lastText) {
          stableCount++;

          if (stableCount >= STABLE_CHECKS) {
            if (!isStillGenerating()) {
              log(`Response complete: ${responseText.length} chars, stable for ${stableCount * STABLE_INTERVAL / 1000}s`);
              return responseText;
            }
            // Still generating — reset but keep lastText
            stableCount = 0;
          }
        } else {
          stableCount = 0;
          lastText = responseText;
        }
      }

      // Periodic status log
      if (elapsed - lastLogTime >= 15) {
        lastLogTime = elapsed;
        log(`Waiting... ${elapsed}s, ${responseText.length} chars, stable=${stableCount}, generating=${isStillGenerating()}`);
      }
    }

    log(`TIMEOUT (${MAX_WAIT/1000}s), returning partial: ${lastText.length} chars`);
    return lastText;
  }

  // ── Process a task ───────────────────────────────────────────────────
  async function processTask(task) {
    const { task_id, prompt, pdf_base64, pdf_name } = task;
    log(`=== Task: ${task_id} ===`);
    busy = true;
    updatePanel();

    try {
      // ACK the task
      try { await serverPost("/ack", { task_id }); } catch {}

      // Phase 1: Navigate to new chat if needed
      if (!isOnNewChatPage()) {
        log("Navigating to new chat...");
        saveTaskState(task);
        setTaskPhase("navigating");
        window.location.href = "https://chatgpt.com/";
        // Script will re-initialize on new page; check savedTask
        return;
      }

      setTaskPhase("processing");

      // Wait for prompt input to appear
      let retries = 0;
      while (!findPromptInput() && retries < 30) {
        await sleep(1000);
        retries++;
      }
      if (!findPromptInput()) {
        throw new Error("Prompt input not found after 30s wait");
      }
      log("Page ready");

      // Upload PDF if present
      if (pdf_base64) {
        await uploadPDF(pdf_base64, pdf_name || "paper.pdf");
      }

      // Enter prompt
      const entered = await enterPrompt(prompt);
      if (!entered) {
        throw new Error("Failed to enter prompt text");
      }

      // Store prompt text for anchor-based response detection
      setSentPrompt(prompt);

      // Send
      const sent = await clickSend();
      if (!sent) {
        throw new Error("Failed to click send");
      }

      // Take post-send snapshot (captures page state before response appears)
      await takePostSendSnapshot();

      // Wait for response
      await sleep(5000); // Additional delay for ChatGPT to start generating
      const response = await waitForResponse();

      if (!response || response.length < 5) {
        throw new Error(`Response too short or empty (${response?.length || 0} chars)`);
      }

      // Post result
      await serverPost("/result", {
        task_id,
        response,
        model: task.model || "unknown",
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
      if (!busy) {
        try {
          const task = await serverGet("/task");
          if (task && task.task_id && task.status !== "idle") {
            await processTask(task);
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
    log("Oracle Bridge v2.6 loaded");

    // Check if we have a saved task from a page navigation
    const savedTask = loadTaskState();
    const phase = getTaskPhase();

    if (savedTask && phase === "navigating") {
      log(`Resuming task after navigation: ${savedTask.task_id}`);
      // We navigated to new chat page — now process the task
      await sleep(3000); // Let page load
      await processTask(savedTask);
    }

    // Start polling
    pollLoop();
  }

  // Run after page is ready
  if (document.readyState === "complete") {
    setTimeout(init, 2000);
  } else {
    window.addEventListener("load", () => setTimeout(init, 2000));
  }
})();
