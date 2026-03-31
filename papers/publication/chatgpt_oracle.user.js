// ==UserScript==
// @name         ChatGPT Oracle Bridge
// @namespace    omega-automath
// @version      2.0
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
  const MAX_WAIT = 900000;        // 15 minutes

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
    panel.innerHTML = `<b>[Oracle Bridge v2]</b> ${busy ? "BUSY" : "idle"}<hr style="border-color:#333;margin:4px 0">${lines}`;
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
    for (const sel of [
      "button[data-testid='send-button']",
      "button[data-testid='composer-send-button']",
      "button[aria-label='Send prompt']",
      "button[aria-label='Send']",
    ]) {
      const el = document.querySelector(sel);
      if (el && !el.disabled) return el;
    }
    // Broader: any non-disabled button inside the composer form
    const form = document.querySelector("form");
    if (form) {
      for (const btn of form.querySelectorAll("button")) {
        if (!btn.disabled && btn.querySelector("svg")) return btn;
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

    // Strategy 4: Direct innerHTML (last resort — may not trigger React state)
    if (!success) {
      const escaped = text
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/\n/g, "<br>");
      input.innerHTML = `<p>${escaped}</p>`;
      input.dispatchEvent(new Event("input", { bubbles: true }));
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

    // Wait up to 30 seconds for send button to become enabled
    // (it stays disabled while PDF is uploading)
    log("Waiting for send button to be ready...");
    for (let i = 0; i < 60; i++) {
      const btn = findSendButton();
      if (btn && !btn.disabled) {
        btn.click();
        log("Send button clicked");
        return true;
      }
      if (i > 0 && i % 10 === 0) {
        log(`Send button not ready yet... ${i * 0.5}s`);
      }
      await sleep(500);
    }

    // Fallback: Enter key
    const input = findPromptInput();
    if (input) {
      log("Send: trying Enter key...");
      input.dispatchEvent(new KeyboardEvent("keydown", {
        key: "Enter", code: "Enter", keyCode: 13,
        bubbles: true, cancelable: true,
      }));
      await sleep(200);
      input.dispatchEvent(new KeyboardEvent("keyup", {
        key: "Enter", code: "Enter", keyCode: 13,
        bubbles: true, cancelable: true,
      }));
      return true;
    }

    log("ERROR: cannot send after 30s wait");
    return false;
  }

  // ── Wait for response to complete ────────────────────────────────────
  async function waitForResponse() {
    log("Waiting for ChatGPT response...");

    const startTime = Date.now();
    let lastText = "";
    let stableCount = 0;
    let lastLogTime = 0;

    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);

      // Try many selectors for response content
      let responseText = "";
      const selectors = [
        "[data-message-author-role='assistant'] .markdown",
        "[data-message-author-role='assistant'] .whitespace-pre-wrap",
        "[data-message-author-role='assistant']",
        ".agent-turn .markdown",
        "div[class*='markdown']",
      ];

      for (const sel of selectors) {
        const els = document.querySelectorAll(sel);
        if (els.length > 0) {
          // Get the last (most recent) response
          const text = els[els.length - 1].innerText?.trim() || "";
          if (text.length > responseText.length) {
            responseText = text;
          }
        }
      }

      if (responseText.length > 0) {
        if (responseText === lastText) {
          stableCount++;

          if (stableCount >= STABLE_CHECKS) {
            // Verify generation is done
            const isGenerating =
              document.querySelector("button[aria-label='Stop generating']") ||
              document.querySelector("button[aria-label='Stop streaming']") ||
              document.querySelector("[class*='result-streaming']") ||
              document.querySelector("[class*='thinking']");

            if (!isGenerating) {
              log(`Response complete: ${responseText.length} chars`);
              return responseText;
            }
            // Still generating, reset
            stableCount = 0;
          }
        } else {
          stableCount = 0;
          lastText = responseText;
        }
      }

      // Periodic status log
      const elapsed = Math.floor((Date.now() - startTime) / 1000);
      if (elapsed - lastLogTime >= 30) {
        lastLogTime = elapsed;
        log(`Waiting... ${elapsed}s, ${responseText.length} chars, stable=${stableCount}`);
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

      // Send
      const sent = await clickSend();
      if (!sent) {
        throw new Error("Failed to click send");
      }

      // Wait for response
      await sleep(5000); // Initial delay for ChatGPT to start thinking
      const response = await waitForResponse();

      if (!response || response.length < 20) {
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
    log("Oracle Bridge v2 loaded");

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
