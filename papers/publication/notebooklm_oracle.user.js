// ==UserScript==
// @name         NotebookLM Oracle Bridge
// @namespace    omega-automath
// @version      1.0
// @description  Bridges local notebooklm_server.py with NotebookLM for automated content generation
// @match        https://notebooklm.google.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @connect      localhost
// @connect      127.0.0.1
// @run-at       document-idle
// ==/UserScript==

(function () {
  "use strict";

  const SERVER = "http://localhost:8766";
  const POLL_INTERVAL = 30000;    // poll every 30s
  const STABLE_CHECKS = 3;        // content stable for 3 checks
  const STABLE_INTERVAL = 30000;  // check every 30s
  const MAX_WAIT = 1800000;       // 30 min max for generation

  let busy = false;
  let active = GM_getValue("nlm_active", false); // starts PAUSED

  // ── Logging ──────────────────────────────────────────────────────────
  const logHistory = [];
  function log(msg) {
    const ts = new Date().toLocaleTimeString();
    const entry = `${ts} ${msg}`;
    console.log(`[nlm-oracle] ${entry}`);
    logHistory.push(entry);
    if (logHistory.length > 20) logHistory.shift();
    updatePanel();
  }

  function toggleActive() {
    active = !active;
    GM_setValue("nlm_active", active);
    log(active ? "ACTIVATED — polling will start" : "PAUSED — your NotebookLM is free");
    updatePanel();
  }

  // ── Status panel ─────────────────────────────────────────────────────
  let panel = null;
  function ensurePanel() {
    if (panel && document.body.contains(panel)) return;
    panel = document.createElement("div");
    panel.id = "nlm-oracle-panel";
    panel.style.cssText = `
      position: fixed; top: 12px; right: 12px; z-index: 99999;
      background: #1a2e1a; color: #0f0; font-family: monospace; font-size: 11px;
      padding: 8px 12px; border-radius: 6px; max-width: 420px; max-height: 300px;
      overflow-y: auto; box-shadow: 0 2px 12px rgba(0,0,0,0.5); opacity: 0.92;
      line-height: 1.4;
    `;
    document.body.appendChild(panel);
  }

  function el(tag, style, text) {
    const e = document.createElement(tag);
    if (style) e.style.cssText = style;
    if (text) e.textContent = text;
    return e;
  }

  function updatePanel() {
    ensurePanel();
    // Clear panel without innerHTML
    while (panel.firstChild) panel.removeChild(panel.firstChild);

    const statusColor = active ? (busy ? "#ff0" : "#0f0") : "#f55";
    const statusText = active ? (busy ? "BUSY" : "ACTIVE") : "PAUSED";
    const btnText = active ? "Pause" : "Start";
    const btnColor = active ? "#f55" : "#0f0";

    // Header row
    const header = el("div", "display:flex;justify-content:space-between;align-items:center;gap:8px");
    header.appendChild(el("b", null, "[NLM Oracle v1.1]"));
    header.appendChild(el("span", `color:${statusColor};font-weight:bold`, statusText));
    const btn = el("button", `background:${btnColor};color:#000;border:none;border-radius:3px;padding:2px 8px;cursor:pointer;font-size:11px;font-weight:bold`, btnText);
    btn.addEventListener("click", toggleActive);
    header.appendChild(btn);
    panel.appendChild(header);

    // Divider
    const hr = el("hr", "border-color:#333;margin:4px 0");
    panel.appendChild(hr);

    // Log lines
    for (const line of logHistory.slice(-10)) {
      panel.appendChild(el("div", null, line));
    }
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

  // ── NotebookLM DOM helpers ──────────────────────────────────────────

  /**
   * NotebookLM UI structure (2025-2026):
   * - Landing page: list of notebooks, "New notebook" button
   * - Notebook page: left sidebar (Sources), center (chat/study guide), right (Audio Overview)
   * - Sources panel: "Add source" button, list of uploaded sources
   * - Chat: input textarea + send button
   * - Audio Overview: "Generate" button → plays audio
   * - Study Guide: accessible from notebook actions
   */

  function findChatInput() {
    for (const sel of [
      "textarea",
      "div[contenteditable='true']",
      "input[type='text']",
      "[role='textbox']",
    ]) {
      const el = document.querySelector(sel);
      if (el) return el;
    }
    return null;
  }

  function findButtonByText(text, opts = {}) {
    const { exact = false, tag = "button" } = opts;
    const buttons = document.querySelectorAll(tag);
    for (const btn of buttons) {
      const btnText = (btn.textContent || "").trim();
      if (exact ? btnText === text : btnText.toLowerCase().includes(text.toLowerCase())) {
        if (!btn.disabled) return btn;
      }
    }
    // Also check mat-button, a[role=button], etc.
    const roleButtons = document.querySelectorAll("[role='button']");
    for (const btn of roleButtons) {
      const btnText = (btn.textContent || "").trim();
      if (exact ? btnText === text : btnText.toLowerCase().includes(text.toLowerCase())) {
        return btn;
      }
    }
    return null;
  }

  function isOnNotebookPage() {
    // On a notebook page, URL contains /notebook/
    return window.location.href.includes("/notebook/");
  }

  function isOnLandingPage() {
    return !isOnNotebookPage();
  }

  // ── Source upload ────────────────────────────────────────────────────

  function makeFile(base64Data, fileName) {
    const byteChars = atob(base64Data);
    const byteArray = new Uint8Array(byteChars.length);
    for (let i = 0; i < byteChars.length; i++) {
      byteArray[i] = byteChars.charCodeAt(i);
    }
    return new File([byteArray], fileName, { type: "application/pdf" });
  }

  function findAllByText(text) {
    const results = [];
    const walk = document.createTreeWalker(document.body, NodeFilter.SHOW_ELEMENT);
    while (walk.nextNode()) {
      const n = walk.currentNode;
      const t = (n.textContent || "").trim().toLowerCase();
      if (t.includes(text.toLowerCase()) && t.length < text.length + 30) {
        results.push(n);
      }
    }
    return results;
  }

  async function tryInjectFile(file) {
    // Method 1: find any file input on the page (may be hidden)
    const inputs = document.querySelectorAll("input[type='file']");
    for (const input of inputs) {
      try {
        const dt = new DataTransfer();
        dt.items.add(file);
        input.files = dt.files;
        input.dispatchEvent(new Event("change", { bubbles: true }));
        input.dispatchEvent(new Event("input", { bubbles: true }));
        log(`PDF injected via file input (${input.accept || "any"})`);
        return true;
      } catch (e) {
        log(`File input failed: ${e.message}`);
      }
    }
    return false;
  }

  async function uploadPDFSource(base64Data, fileName) {
    log(`Uploading: ${fileName} (${(base64Data.length * 0.75 / 1024).toFixed(0)} KB)`);
    const file = makeFile(base64Data, fileName);

    // Step 1: Click "Add source" button
    const addBtn = findButtonByText("Add source") ||
                   findButtonByText("add source") ||
                   document.querySelector("button[aria-label*='source' i]") ||
                   document.querySelector("button[aria-label*='Source']") ||
                   document.querySelector("button[aria-label*='add' i]");

    if (addBtn) {
      log("Step 1: Clicking 'Add source'...");
      addBtn.click();
      await sleep(2000);
    } else {
      log("WARN: 'Add source' button not found");
    }

    // Step 2: In the dialog, click "Upload" / "File upload" / "PDF" option
    // NotebookLM shows a dialog with source type choices
    const uploadOption = findButtonByText("File upload") ||
                         findButtonByText("Upload") ||
                         findButtonByText("PDF") ||
                         findButtonByText("upload file");

    // Also try clickable elements (not just buttons)
    let uploadEl = uploadOption;
    if (!uploadEl) {
      const candidates = findAllByText("upload");
      if (candidates.length > 0) {
        uploadEl = candidates[candidates.length - 1]; // last match usually the dialog option
      }
    }
    if (!uploadEl) {
      const candidates = findAllByText("file");
      for (const c of candidates) {
        if ((c.textContent || "").toLowerCase().includes("upload")) {
          uploadEl = c;
          break;
        }
      }
    }

    if (uploadEl) {
      log(`Step 2: Clicking '${(uploadEl.textContent || "").trim().slice(0, 30)}'...`);
      uploadEl.click();
      await sleep(2000);
    } else {
      log("WARN: Upload option not found in dialog");
    }

    // Step 3: Try to inject file into any file input that appeared
    if (await tryInjectFile(file)) {
      await sleep(8000); // wait for processing
      // Look for confirm/insert button
      const confirmBtn = findButtonByText("Insert") ||
                         findButtonByText("Add") ||
                         findButtonByText("Upload") ||
                         findButtonByText("Done");
      if (confirmBtn) {
        log(`Step 3: Clicking '${(confirmBtn.textContent || "").trim()}'`);
        confirmBtn.click();
        await sleep(5000);
      }
      log("PDF upload complete");
      return true;
    }

    // Step 4: Fallback — try drag-drop on various targets
    log("Step 3 fallback: trying drag-drop...");
    const targets = [
      ...document.querySelectorAll("[class*='drop']"),
      ...document.querySelectorAll("[class*='upload']"),
      ...document.querySelectorAll("[class*='source']"),
      ...document.querySelectorAll("[role='dialog']"),
      document.querySelector("main"),
    ].filter(Boolean);

    for (const target of targets) {
      const dt = new DataTransfer();
      dt.items.add(file);
      for (const evtType of ["dragenter", "dragover", "drop"]) {
        target.dispatchEvent(new DragEvent(evtType, {
          bubbles: true, cancelable: true, dataTransfer: dt,
        }));
        await sleep(200);
      }
    }
    log(`Drag-drop attempted on ${targets.length} targets`);
    await sleep(5000);

    // Check if something appeared (new source in sidebar)
    return true;
  }

  // ── Create new notebook ─────────────────────────────────────────────

  async function createNewNotebook() {
    log("Creating new notebook...");

    const newBtn = findButtonByText("New notebook") ||
                   findButtonByText("Create") ||
                   document.querySelector("button[aria-label*='new']") ||
                   document.querySelector("button[aria-label*='New']") ||
                   document.querySelector("button[aria-label*='create']");

    if (newBtn) {
      newBtn.click();
      log("Clicked 'New notebook'");
      await sleep(3000);

      // Wait for notebook page to load
      for (let i = 0; i < 30; i++) {
        if (isOnNotebookPage()) {
          log("Notebook page loaded");
          return true;
        }
        await sleep(1000);
      }
    }

    log("Could not create notebook — may need manual intervention");
    return false;
  }

  // ── Chat interaction ────────────────────────────────────────────────

  async function sendChatMessage(text) {
    log(`Sending chat message (${text.length} chars)...`);

    const input = findChatInput();
    if (!input) {
      log("ERROR: chat input not found");
      return false;
    }

    input.focus();
    await sleep(300);

    // Set value based on element type
    if (input.tagName === "TEXTAREA" || input.tagName === "INPUT") {
      // Standard input — use native value setter for React
      const nativeInputValueSetter = Object.getOwnPropertyDescriptor(
        window.HTMLTextAreaElement.prototype, "value"
      )?.set || Object.getOwnPropertyDescriptor(
        window.HTMLInputElement.prototype, "value"
      )?.set;

      if (nativeInputValueSetter) {
        nativeInputValueSetter.call(input, text);
      } else {
        input.value = text;
      }
      input.dispatchEvent(new Event("input", { bubbles: true }));
      input.dispatchEvent(new Event("change", { bubbles: true }));
    } else {
      // Contenteditable — use execCommand
      document.execCommand("selectAll", false, null);
      document.execCommand("delete", false, null);
      document.execCommand("insertText", false, text);
    }

    await sleep(500);

    // Find and click send button
    const sendBtn = document.querySelector("button[aria-label='Send']") ||
                    document.querySelector("button[aria-label='Send message']") ||
                    findButtonByText("Send") ||
                    document.querySelector("button[type='submit']");

    if (sendBtn && !sendBtn.disabled) {
      sendBtn.click();
      log("Chat message sent");
      return true;
    }

    // Try Enter key
    input.dispatchEvent(new KeyboardEvent("keydown", {
      key: "Enter", code: "Enter", keyCode: 13, bubbles: true,
    }));
    await sleep(100);
    input.dispatchEvent(new KeyboardEvent("keyup", {
      key: "Enter", code: "Enter", keyCode: 13, bubbles: true,
    }));

    log("Chat: sent via Enter key");
    return true;
  }

  async function waitForChatResponse() {
    log("Waiting for NotebookLM response...");
    const startTime = Date.now();
    let lastText = "";
    let stableCount = 0;

    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);

      // Try to extract the latest response
      // NotebookLM uses Angular Material — look for response containers
      const responseEls = document.querySelectorAll(
        "[class*='response'], [class*='message'], [class*='answer'], " +
        "[class*='chat-bubble'], [class*='markdown'], [class*='prose']"
      );

      let responseText = "";
      if (responseEls.length > 0) {
        const last = responseEls[responseEls.length - 1];
        responseText = (last.innerText || "").trim();
      }

      // Fallback: grab text from main content area
      if (responseText.length < 50) {
        const main = document.querySelector("main") || document.querySelector("[role='main']");
        if (main) {
          responseText = (main.innerText || "").trim();
        }
      }

      const elapsed = Math.floor((Date.now() - startTime) / 1000);

      if (responseText.length >= 50) {
        if (responseText === lastText) {
          stableCount++;
          if (stableCount >= STABLE_CHECKS) {
            log(`Response complete: ${responseText.length} chars (stable ${stableCount * STABLE_INTERVAL / 1000}s)`);
            return responseText;
          }
        } else {
          stableCount = 0;
          lastText = responseText;
        }
      }

      if (elapsed % 60 === 0 && elapsed > 0) {
        log(`Waiting... ${elapsed}s, text=${responseText.length}, stable=${stableCount}`);
      }
    }

    log(`TIMEOUT, returning partial: ${lastText.length} chars`);
    return lastText;
  }

  // ── Audio Overview generation ───────────────────────────────────────

  async function generateAudioOverview() {
    log("Generating Audio Overview...");

    // Find the "Generate" button in the Audio Overview section
    const genBtn = findButtonByText("Generate") ||
                   findButtonByText("Create audio") ||
                   document.querySelector("button[aria-label*='audio']") ||
                   document.querySelector("button[aria-label*='Audio']") ||
                   document.querySelector("button[aria-label*='generate']");

    if (!genBtn) {
      log("ERROR: Audio Overview 'Generate' button not found");
      return null;
    }

    genBtn.click();
    log("Clicked 'Generate' — waiting for audio...");

    // Wait for audio to be generated (can take several minutes)
    for (let i = 0; i < 120; i++) { // up to 60 min
      await sleep(30000);
      const elapsed = (i + 1) * 30;

      // Check for completion indicators
      const playBtn = document.querySelector("button[aria-label*='play']") ||
                      document.querySelector("button[aria-label*='Play']") ||
                      findButtonByText("Play");
      const audioEl = document.querySelector("audio");

      if (playBtn || audioEl) {
        log(`Audio Overview generated (${elapsed}s)`);
        return "Audio Overview generated successfully";
      }

      // Check for error
      const error = document.querySelector("[class*='error']");
      if (error && (error.textContent || "").toLowerCase().includes("error")) {
        log(`Audio generation error: ${(error.textContent || "").slice(0, 200)}`);
        return `ERROR: ${(error.textContent || "").slice(0, 500)}`;
      }

      if (elapsed % 120 === 0) {
        log(`Audio generation in progress... ${elapsed}s`);
      }
    }

    log("Audio generation TIMEOUT");
    return "ERROR: Audio generation timeout (60 min)";
  }

  // ── Process task ────────────────────────────────────────────────────

  async function processTask(task) {
    const { task_id, task_type, pdf_base64, pdf_name, prompt } = task;
    log(`=== Task: ${task_id} (${task_type || "unknown"}) ===`);
    busy = true;
    updatePanel();

    try {
      // ACK
      try { await serverPost("/ack", { task_id }); } catch {}

      let response = "";

      switch (task_type) {
        case "audio_overview": {
          // 1. Create notebook if needed
          if (isOnLandingPage()) {
            await createNewNotebook();
          }
          // 2. Upload PDF source
          if (pdf_base64) {
            await uploadPDFSource(pdf_base64, pdf_name || "paper.pdf");
            await sleep(10000); // Wait for source processing
          }
          // 3. Generate audio overview
          response = await generateAudioOverview() || "ERROR: No audio generated";
          break;
        }

        case "chat":
        case "study_guide":
        case "review": {
          // 1. Create notebook if needed
          if (isOnLandingPage()) {
            await createNewNotebook();
          }
          // 2. Upload PDF source if provided
          if (pdf_base64) {
            await uploadPDFSource(pdf_base64, pdf_name || "paper.pdf");
            await sleep(10000);
          }
          // 3. Send chat message
          const chatPrompt = prompt || "Please provide a comprehensive study guide for this document.";
          await sendChatMessage(chatPrompt);
          // 4. Wait for response
          response = await waitForChatResponse();
          if (!response || response.length < 10) {
            response = "ERROR: No response captured";
          }
          break;
        }

        default:
          response = `ERROR: Unknown task_type '${task_type}'`;
          log(response);
      }

      // Post result
      await serverPost("/result", {
        task_id,
        response,
        task_type: task_type || "unknown",
      });

      log(`DONE: ${task_id} (${response.length} chars)`);

    } catch (err) {
      log(`ERROR: ${err.message}`);
      try {
        await serverPost("/result", {
          task_id,
          response: `ERROR: ${err.message}`,
          task_type: task_type || "unknown",
        });
      } catch {}
    } finally {
      busy = false;
      updatePanel();
    }
  }

  // ── Main loop ────────────────────────────────────────────────────────
  async function pollLoop() {
    while (true) {
      if (active && !busy) {
        try {
          const task = await serverGet("/task");
          if (task && task.task_id && task.status !== "idle") {
            await processTask(task);
          }
        } catch (err) {
          if (logHistory.length === 0 || !logHistory[logHistory.length - 1].includes("unreachable")) {
            log("Server unreachable");
          }
        }
      }
      await sleep(POLL_INTERVAL);
    }
  }

  // ── Bootstrap ──────────────────────────────────────────────────────
  async function init() {
    log(`NLM Oracle v1.0 loaded — ${active ? "ACTIVE" : "PAUSED (click Start to activate)"}`);
    pollLoop();
  }

  if (document.readyState === "complete") {
    setTimeout(init, 2000);
  } else {
    window.addEventListener("load", () => setTimeout(init, 2000));
  }
})();
