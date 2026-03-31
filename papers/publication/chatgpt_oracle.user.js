// ==UserScript==
// @name         ChatGPT Oracle Bridge
// @namespace    omega-automath
// @version      1.0
// @description  Bridges local oracle_server.py with ChatGPT Pro for automated paper review
// @match        https://chatgpt.com/*
// @match        https://chat.openai.com/*
// @grant        GM_xmlhttpRequest
// @connect      localhost
// @connect      127.0.0.1
// @run-at       document-idle
// ==/UserScript==

(function () {
  "use strict";

  const SERVER = "http://localhost:8765";
  const POLL_INTERVAL = 5000; // 5 seconds
  const STABLE_CHECKS = 4; // response must be stable for 4 consecutive checks
  const STABLE_INTERVAL = 3000; // check every 3 seconds
  const MAX_WAIT = 900000; // 15 minutes max wait for response

  let currentTask = null;
  let busy = false;

  // ── Logging ──────────────────────────────────────────────────────────
  function log(msg) {
    console.log(`[oracle] ${msg}`);
    updatePanel(msg);
  }

  // ── Status panel (floating overlay) ──────────────────────────────────
  let panel = null;
  function createPanel() {
    panel = document.createElement("div");
    panel.id = "oracle-panel";
    panel.style.cssText = `
      position: fixed; bottom: 12px; right: 12px; z-index: 99999;
      background: #1a1a2e; color: #0f0; font-family: monospace; font-size: 12px;
      padding: 8px 12px; border-radius: 6px; max-width: 380px;
      box-shadow: 0 2px 12px rgba(0,0,0,0.5); opacity: 0.92;
      cursor: move; user-select: none;
    `;
    panel.innerHTML = `<b>[Oracle Bridge]</b> idle — polling ${SERVER}`;
    document.body.appendChild(panel);

    // Make draggable
    let dragging = false, dx = 0, dy = 0;
    panel.addEventListener("mousedown", (e) => {
      dragging = true;
      dx = e.clientX - panel.getBoundingClientRect().left;
      dy = e.clientY - panel.getBoundingClientRect().top;
    });
    document.addEventListener("mousemove", (e) => {
      if (!dragging) return;
      panel.style.left = (e.clientX - dx) + "px";
      panel.style.top = (e.clientY - dy) + "px";
      panel.style.right = "auto";
      panel.style.bottom = "auto";
    });
    document.addEventListener("mouseup", () => { dragging = false; });
  }

  function updatePanel(msg) {
    if (!panel) createPanel();
    const time = new Date().toLocaleTimeString();
    panel.innerHTML = `<b>[Oracle Bridge]</b> ${time}<br>${msg}`;
  }

  // ── HTTP helpers using GM_xmlhttpRequest (bypasses CORS) ─────────────
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
        onerror: (e) => reject(e),
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
        onerror: (e) => reject(e),
        ontimeout: () => reject(new Error("timeout")),
      });
    });
  }

  // ── Wait helper ──────────────────────────────────────────────────────
  function sleep(ms) {
    return new Promise((r) => setTimeout(r, ms));
  }

  // ── Find the prompt input area ───────────────────────────────────────
  function findPromptInput() {
    // ChatGPT uses a contenteditable div with id="prompt-textarea"
    // or a ProseMirror editor
    const selectors = [
      "#prompt-textarea",
      "div[contenteditable='true'][id='prompt-textarea']",
      "div.ProseMirror[contenteditable='true']",
      "textarea[data-id]",
      "div[contenteditable='true']",
    ];
    for (const sel of selectors) {
      const el = document.querySelector(sel);
      if (el) return el;
    }
    return null;
  }

  // ── Find the send button ─────────────────────────────────────────────
  function findSendButton() {
    const selectors = [
      "button[data-testid='send-button']",
      "button[aria-label='Send prompt']",
      "button[data-testid='composer-send-button']",
      // Fallback: find button near the textarea
    ];
    for (const sel of selectors) {
      const el = document.querySelector(sel);
      if (el && !el.disabled) return el;
    }
    // Broader search: any enabled send-like button in the composer
    const buttons = document.querySelectorAll("form button, [class*='composer'] button");
    for (const btn of buttons) {
      const svg = btn.querySelector("svg");
      if (svg && !btn.disabled) {
        // The send button typically has an arrow icon
        const path = svg.querySelector("path");
        if (path) return btn;
      }
    }
    return null;
  }

  // ── Upload PDF from base64 ───────────────────────────────────────────
  async function uploadPDF(base64Data, fileName) {
    log(`Uploading PDF: ${fileName}`);

    // Convert base64 to File object
    const byteChars = atob(base64Data);
    const byteArray = new Uint8Array(byteChars.length);
    for (let i = 0; i < byteChars.length; i++) {
      byteArray[i] = byteChars.charCodeAt(i);
    }
    const blob = new Blob([byteArray], { type: "application/pdf" });
    const file = new File([blob], fileName, { type: "application/pdf" });

    // Find the file input element
    const fileInput = document.querySelector("input[type='file']");
    if (!fileInput) {
      log("WARNING: No file input found, trying drag-drop...");
      return await uploadViaDragDrop(file);
    }

    // Create a DataTransfer to set files on the input
    const dt = new DataTransfer();
    dt.items.add(file);
    fileInput.files = dt.files;

    // Dispatch change event
    fileInput.dispatchEvent(new Event("change", { bubbles: true }));
    log(`PDF injected into file input (${(byteArray.length / 1024).toFixed(0)} KB)`);

    // Wait for upload to process
    await sleep(4000);
    return true;
  }

  // ── Fallback: upload via synthetic drag-drop ─────────────────────────
  async function uploadViaDragDrop(file) {
    // Find the drop target (usually the composer area)
    const dropTarget =
      document.querySelector("[class*='composer']") ||
      document.querySelector("form") ||
      document.querySelector("#prompt-textarea")?.parentElement;

    if (!dropTarget) {
      log("ERROR: Cannot find drop target for PDF");
      return false;
    }

    const dt = new DataTransfer();
    dt.items.add(file);

    const events = ["dragenter", "dragover", "drop"];
    for (const eventType of events) {
      const event = new DragEvent(eventType, {
        bubbles: true,
        cancelable: true,
        dataTransfer: dt,
      });
      dropTarget.dispatchEvent(event);
      await sleep(200);
    }

    log("PDF dropped via drag-drop simulation");
    await sleep(4000);
    return true;
  }

  // ── Enter prompt text ────────────────────────────────────────────────
  async function enterPrompt(text) {
    log(`Entering prompt (${text.length} chars)...`);

    const input = findPromptInput();
    if (!input) {
      log("ERROR: Cannot find prompt input");
      return false;
    }

    // Focus the input
    input.focus();
    await sleep(300);

    // For contenteditable divs (ProseMirror), we need special handling
    if (input.contentEditable === "true") {
      // Clear existing content
      input.innerHTML = "";
      await sleep(100);

      // Use clipboard API for reliable text insertion
      // This handles ProseMirror's internal state correctly
      const clipData = new DataTransfer();
      clipData.setData("text/plain", text);
      const pasteEvent = new ClipboardEvent("paste", {
        bubbles: true,
        cancelable: true,
        clipboardData: clipData,
      });
      input.dispatchEvent(pasteEvent);
      await sleep(300);

      // Verify text was entered
      if (input.textContent.length < 10 && text.length > 10) {
        // Fallback: set innerHTML directly
        log("Paste failed, trying innerHTML fallback...");
        // Escape HTML entities
        const escaped = text
          .replace(/&/g, "&amp;")
          .replace(/</g, "&lt;")
          .replace(/>/g, "&gt;")
          .replace(/\n/g, "<br>");
        input.innerHTML = `<p>${escaped}</p>`;
        input.dispatchEvent(new Event("input", { bubbles: true }));
        await sleep(300);
      }

      // Another fallback: use execCommand
      if (input.textContent.length < 10 && text.length > 10) {
        log("innerHTML failed, trying execCommand...");
        input.focus();
        document.execCommand("selectAll", false, null);
        document.execCommand("insertText", false, text);
        await sleep(300);
      }
    } else {
      // Textarea
      input.value = text;
      input.dispatchEvent(new Event("input", { bubbles: true }));
    }

    log(`Prompt entered (${input.textContent?.length || input.value?.length || 0} chars visible)`);
    return true;
  }

  // ── Click send ───────────────────────────────────────────────────────
  async function clickSend() {
    // Wait a moment for the UI to register the input
    await sleep(500);

    const sendBtn = findSendButton();
    if (sendBtn) {
      sendBtn.click();
      log("Send button clicked");
      return true;
    }

    // Fallback: try pressing Enter in the input
    const input = findPromptInput();
    if (input) {
      input.dispatchEvent(new KeyboardEvent("keydown", {
        key: "Enter", code: "Enter", keyCode: 13,
        bubbles: true, cancelable: true,
      }));
      log("Enter key dispatched (fallback)");
      return true;
    }

    log("ERROR: Cannot find send button or input");
    return false;
  }

  // ── Wait for ChatGPT response to complete ────────────────────────────
  async function waitForResponse() {
    log("Waiting for response...");

    const startTime = Date.now();
    let lastText = "";
    let stableCount = 0;

    while (Date.now() - startTime < MAX_WAIT) {
      await sleep(STABLE_INTERVAL);

      // Find response elements — try multiple selectors for different UI versions
      let responseEls = document.querySelectorAll(
        "[data-message-author-role='assistant'] .markdown"
      );
      if (!responseEls.length) {
        responseEls = document.querySelectorAll(".agent-turn .markdown");
      }
      if (!responseEls.length) {
        responseEls = document.querySelectorAll("[class*='response'] .markdown");
      }
      if (!responseEls.length) {
        responseEls = document.querySelectorAll("[data-message-author-role='assistant']");
      }

      if (responseEls.length > 0) {
        // Get the LAST response (most recent)
        const lastEl = responseEls[responseEls.length - 1];
        const currentText = lastEl.innerText?.trim() || "";

        if (currentText.length > 0 && currentText === lastText) {
          stableCount++;

          if (stableCount >= STABLE_CHECKS) {
            // Also verify no "Stop generating" button exists
            const stopBtn = document.querySelector(
              "button[aria-label='Stop generating'], button[aria-label='Stop streaming']"
            );
            // Check for thinking indicator
            const thinking = document.querySelector(
              "[class*='thinking'], [class*='progress'], [data-testid='thinking']"
            );
            if (!stopBtn && !thinking) {
              log(`Response complete: ${currentText.length} chars`);
              return currentText;
            } else {
              stableCount = 0; // Reset — still generating
            }
          }
        } else {
          stableCount = 0;
          lastText = currentText;
        }

        const elapsed = Math.floor((Date.now() - startTime) / 1000);
        if (elapsed > 0 && elapsed % 30 === 0) {
          log(`Still waiting... ${elapsed}s, ${currentText.length} chars`);
        }
      } else {
        const elapsed = Math.floor((Date.now() - startTime) / 1000);
        if (elapsed > 10 && elapsed % 15 === 0) {
          log(`No response elements yet... ${elapsed}s`);
        }
      }
    }

    log(`TIMEOUT after ${MAX_WAIT / 1000}s`);
    return lastText || "";
  }

  // ── Navigate to a new chat ───────────────────────────────────────────
  async function startNewChat() {
    // Click "New chat" button or navigate
    const newChatBtn = document.querySelector(
      "a[href='/'], nav a[class*='new'], button[class*='new-chat']"
    );
    if (newChatBtn) {
      newChatBtn.click();
      await sleep(2000);
      return;
    }
    // Fallback: navigate directly
    window.location.href = "https://chatgpt.com/";
    await sleep(3000);
  }

  // ── Process a single task ────────────────────────────────────────────
  async function processTask(task) {
    const { task_id, prompt, pdf_base64, pdf_name } = task;
    log(`Processing task: ${task_id}`);
    busy = true;
    currentTask = task;

    try {
      // Acknowledge task
      await serverPost("/ack", { task_id });

      // Start a new chat to avoid context pollution
      await startNewChat();
      await sleep(2000);

      // Wait for page to be ready
      let retries = 0;
      while (!findPromptInput() && retries < 20) {
        await sleep(1000);
        retries++;
      }
      if (!findPromptInput()) {
        throw new Error("Prompt input not found after waiting");
      }

      // Upload PDF if present
      if (pdf_base64) {
        const uploaded = await uploadPDF(pdf_base64, pdf_name || "paper.pdf");
        if (!uploaded) {
          log("WARNING: PDF upload may have failed");
        }
        await sleep(2000);
      }

      // Enter prompt
      const entered = await enterPrompt(prompt);
      if (!entered) {
        throw new Error("Failed to enter prompt");
      }

      // Click send
      const sent = await clickSend();
      if (!sent) {
        throw new Error("Failed to send prompt");
      }

      // Wait for response
      await sleep(3000); // Give ChatGPT a moment to start
      const response = await waitForResponse();

      if (!response) {
        throw new Error("Empty response received");
      }

      // Post result back to server
      await serverPost("/result", {
        task_id,
        response,
        model: task.model || "unknown",
      });

      log(`Task ${task_id} completed (${response.length} chars)`);
    } catch (err) {
      log(`ERROR: ${err.message}`);
      // Post error result
      try {
        await serverPost("/result", {
          task_id,
          response: `ERROR: ${err.message}`,
          model: task.model || "unknown",
        });
      } catch (e) {
        log(`Failed to report error: ${e.message}`);
      }
    } finally {
      busy = false;
      currentTask = null;
    }
  }

  // ── Main polling loop ────────────────────────────────────────────────
  async function pollLoop() {
    while (true) {
      if (!busy) {
        try {
          const task = await serverGet("/task");
          if (task && task.task_id && task.status !== "idle") {
            await processTask(task);
          } else {
            // Idle — show status quietly
            updatePanel(`idle — polling ${SERVER}`);
          }
        } catch (err) {
          // Server not running or unreachable
          updatePanel(`server unreachable (${err.message || "offline"})`);
        }
      }
      await sleep(POLL_INTERVAL);
    }
  }

  // ── Bootstrap ────────────────────────────────────────────────────────
  function init() {
    console.log("[oracle] ChatGPT Oracle Bridge v1.0 loaded");
    createPanel();
    // Start polling after a short delay to let the page settle
    setTimeout(pollLoop, 3000);
  }

  // Wait for page to be ready
  if (document.readyState === "complete") {
    init();
  } else {
    window.addEventListener("load", init);
  }
})();
