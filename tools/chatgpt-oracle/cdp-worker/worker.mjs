#!/usr/bin/env node
// Automath ChatGPT Oracle CDP worker.
//
// This drives a real, logged-in Chrome profile through the Chrome DevTools
// Protocol and speaks the existing local oracle_server.py protocol. It is a
// local replacement for the Tampermonkey userscript worker; the pipeline and
// deterministic publication gates remain unchanged.

import { chromium } from "playwright-core";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { pathToFileURL } from "node:url";

const BASE_URL = (process.env.AUTOMATH_ORACLE_URL || "http://127.0.0.1:8765").replace(/\/$/, "");
const AGENT_ID = process.env.AUTOMATH_AGENT_ID || "oracle_1";
const CDP_URL = process.env.CHROME_CDP_URL || "http://127.0.0.1:9222";
const SCRIPT_VERSION = "cdp-automath-0.1";
const POLL_MS = Number(process.env.AUTOMATH_POLL_MS || 5000);
const STABLE_INTERVAL_MS = Number(process.env.AUTOMATH_STABLE_INTERVAL_MS || 8000);
const MAX_WAIT_MS = Number(process.env.AUTOMATH_MAX_WAIT_MS || 2 * 60 * 60 * 1000);
const HEARTBEAT_MS = Number(process.env.AUTOMATH_HEARTBEAT_MS || 60000);
const UPLOAD_WAIT_MS = Number(process.env.AUTOMATH_UPLOAD_WAIT_MS || 90000);

function log(message) {
  console.log(`[automath-cdp ${AGENT_ID} ${new Date().toISOString()}] ${message}`);
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

function enc(value) {
  return encodeURIComponent(value || "");
}

async function apiGet(pathname) {
  const response = await fetch(`${BASE_URL}${pathname}`);
  if (!response.ok) {
    const error = new Error(`GET ${pathname} -> ${response.status}`);
    error.status = response.status;
    throw error;
  }
  return response.json();
}

async function apiPost(pathname, body) {
  const response = await fetch(`${BASE_URL}${pathname}`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
  if (!response.ok) {
    const text = await response.text().catch(() => "");
    const error = new Error(`POST ${pathname} -> ${response.status} ${text.slice(0, 200)}`);
    error.status = response.status;
    throw error;
  }
  return response.json();
}

async function ack(task_id, phase = "active") {
  try {
    await apiPost("/ack", { task_id, agent_id: AGENT_ID, phase, script_version: SCRIPT_VERSION });
    return false;
  } catch {
    return false;
  }
}

async function postPhase(task_id, phase, detail = "") {
  try {
    await apiPost("/phase", { task_id, agent_id: AGENT_ID, phase, detail, script_version: SCRIPT_VERSION });
  } catch (err) {
    log(`phase post failed: ${err.message}`);
  }
}

async function postResult(task, response, page, model = "") {
  const task_id = task.task_id;
  return apiPost("/result", {
    task_id,
    agent_id: AGENT_ID,
    response,
    chatgpt_url: page.url(),
    model: model || task.model || "",
    script_version: SCRIPT_VERSION,
  });
}

async function releaseTask(task, reason) {
  try {
    await apiPost("/release", {
      task_id: task.task_id,
      agent_id: AGENT_ID,
      reason,
      script_version: SCRIPT_VERSION,
    });
  } catch (err) {
    log(`release failed: ${err.message}`);
  }
}

async function pinConversationUrl(task, page) {
  if (!/\/c\/[A-Za-z0-9-]{6,}/.test(page.url())) return;
  try {
    await apiPost("/pin-conv-url", {
      task_id: task.task_id,
      agent_id: AGENT_ID,
      chatgpt_url: page.url(),
      script_version: SCRIPT_VERSION,
    });
  } catch (err) {
    log(`pin-conv-url failed: ${err.message}`);
  }
}

const DOM_CORE = `
window.__automathOracle = (function () {
  function extractTextWithMath(el) {
    if (!el) return "";
    const clone = el.cloneNode(true);
    for (const ann of Array.from(clone.querySelectorAll('annotation[encoding="application/x-tex"]'))) {
      const latex = (ann.textContent || "").trim();
      if (!latex) continue;
      const outer = ann.closest(".katex-display, .katex") || ann.parentElement;
      if (outer) {
        const display = outer.classList.contains("katex-display") ||
          (outer.parentElement && outer.parentElement.classList.contains("katex-display"));
        outer.replaceWith(document.createTextNode(display ? "\\n$$" + latex + "$$\\n" : " $" + latex + "$ "));
      }
    }
    for (const mjx of Array.from(clone.querySelectorAll("mjx-container"))) {
      let latex = "";
      const ann = mjx.querySelector('annotation[encoding*="TeX"]');
      if (ann) latex = (ann.textContent || "").trim();
      if (!latex) latex = mjx.getAttribute("aria-label") || mjx.getAttribute("data-latex") || "";
      if (latex) {
        const display = mjx.getAttribute("display") === "true" || mjx.getAttribute("data-display") === "block";
        mjx.replaceWith(document.createTextNode(display ? "\\n$$" + latex + "$$\\n" : " $" + latex + "$ "));
      }
    }
    for (const math of Array.from(clone.querySelectorAll("math"))) {
      const alt = math.getAttribute("alttext") || "";
      if (alt) math.replaceWith(document.createTextNode(" $" + alt + "$ "));
    }
    return (clone.innerText || clone.textContent || "").trim();
  }

  const CHROME_RE = /^(ChatGPT|You said:|ChatGPT said:|Copy code|Copy|Share|Regenerate|Ask anything|Send a message|GPT-|4o|o\\d|Pro|Extended Pro)$/i;
  const REASONING_RE = /^(Thought for\\s+\\d+|Pro Extended|Show less|Show more|Thinking|Reasoning)$/i;

  function cleanText(text) {
    return (text || "").split("\\n").filter((line) => {
      const t = line.trim();
      if (!t) return true;
      if (CHROME_RE.test(t)) return false;
      if (REASONING_RE.test(t)) return false;
      return true;
    }).join("\\n").trim();
  }

  function isStillGenerating() {
    const dom = !!(
      document.querySelector("button[aria-label='Stop generating']") ||
      document.querySelector("button[aria-label='Stop streaming']") ||
      document.querySelector("button[data-testid='stop-button']") ||
      document.querySelector("[role='progressbar']") ||
      document.querySelector("[class*='result-streaming']") ||
      document.querySelector("[class*='streaming']")
    );
    if (dom) return true;
    const main = document.querySelector("main");
    const txt = main ? (main.innerText || "") : "";
    return /Pro thinking|Extended Pro|Reasoning/.test(txt) && !/Thought for\\s+\\d+/i.test(txt);
  }

  function assistantCount() {
    return document.querySelectorAll("[data-message-author-role='assistant']").length;
  }

  function extractResponse() {
    const main = document.querySelector("main") || document.body;
    const els = main.querySelectorAll("[data-message-author-role='assistant']");
    if (!els.length) return "";
    return cleanText(extractTextWithMath(els[els.length - 1]));
  }

  function uploadState() {
    const uploading = !!(
      document.querySelector("[class*='uploading']") ||
      document.querySelector("[class*='progress']") ||
      document.querySelector("[role='progressbar']") ||
      document.querySelector("[class*='loading']")
    );
    const attached = !!(
      document.querySelector("[class*='attachment']") ||
      document.querySelector("[class*='file-chip']") ||
      document.querySelector("[data-testid*='attachment']") ||
      document.querySelector("[class*='uploaded']") ||
      document.querySelector("img[alt*='pdf']") ||
      document.querySelector("[class*='file']")
    );
    const send = document.querySelector("button[data-testid='send-button'], button[aria-label='Send prompt'], button[aria-label='Send message']");
    return { uploading, attached, sendEnabled: !!(send && !send.disabled) };
  }

  function promptDebug() {
    const input = document.querySelector("#prompt-textarea, div[contenteditable='true'][role='textbox'], textarea[data-testid='prompt-textarea']");
    const file = document.querySelector("input[type='file']");
    return "prompt=" + !!input + " file=" + !!file + " assistants=" + assistantCount() + " url=" + location.href;
  }

  return { isStillGenerating, assistantCount, extractResponse, uploadState, promptDebug, cleanText };
})();
`;

async function installDomCore(page) {
  await page.addInitScript({ content: DOM_CORE });
  try {
    await page.evaluate(DOM_CORE);
  } catch {
    // The init script covers the next load if the page is navigating.
  }
}

function isChatGptUrl(url) {
  return /^https:\/\/(chatgpt\.com|chat\.openai\.com)\//.test(url || "");
}

function agentTabMarker(agentId = AGENT_ID) {
  return String(agentId || "oracle_1").replace(/^oracle_/, "") || "1";
}

function isAgentChatPage(page, agentId = AGENT_ID) {
  const url = page.url();
  if (!isChatGptUrl(url)) return false;
  try {
    const parsed = new URL(url);
    return parsed.searchParams.get("oracle") === agentTabMarker(agentId);
  } catch {
    return false;
  }
}

async function getChatPage(context, agentId = AGENT_ID) {
  let page = context.pages().find((p) => isAgentChatPage(p, agentId));
  if (!page) {
    page = await context.newPage();
    await page.goto(`https://chatgpt.com/?oracle=${enc(agentTabMarker(agentId))}`, {
      waitUntil: "domcontentloaded",
    });
  }
  await installDomCore(page);
  return page;
}

function normalizedProjectUrl(task) {
  const raw = String(task.project_url || "").trim();
  if (!raw) return "";
  try {
    const url = new URL(raw);
    if (!/^https:\/\/(chatgpt\.com|chat\.openai\.com)$/.test(url.origin)) return "";
    const projectMatch = url.pathname.match(/^(\/g\/g-p-[a-z0-9-]+(?:-[^/?#]+)?)(?:\/(?:project|c\/[a-z0-9-]+))?\/?$/i);
    if (projectMatch) {
      url.pathname = `${projectMatch[1]}/project`;
    } else {
      url.pathname = url.pathname.replace(/\/c\/[a-z0-9-]+\/?$/i, "");
    }
    url.search = "";
    url.hash = "";
    return url.href;
  } catch {
    return "";
  }
}

function taskStartUrl(task) {
  const agentNum = AGENT_ID.replace(/^oracle_/, "");
  if (task.is_followup && task.conversation_url) {
    try {
      const url = new URL(task.conversation_url);
      if (/^https:\/\/(chatgpt\.com|chat\.openai\.com)$/.test(url.origin)) {
        url.searchParams.set("oracle", agentNum);
        return url.href;
      }
    } catch {
      // Fall through.
    }
  }
  const projectUrl = normalizedProjectUrl(task);
  if (projectUrl) {
    const url = new URL(projectUrl);
    url.searchParams.set("oracle", agentNum);
    return url.href;
  }
  return `https://chatgpt.com/?oracle=${enc(agentNum)}`;
}

async function navigateForTask(page, task) {
  const target = taskStartUrl(task);
  const current = page.url();
  const needsNavigation = task.is_followup || normalizedProjectUrl(task) || !isChatGptUrl(current);
  if (!needsNavigation) return;
  if (current.replace(/[#?].*$/, "") === target.replace(/[#?].*$/, "")) return;
  await postPhase(task.task_id, "navigating", target.slice(0, 300));
  await page.goto(target, { waitUntil: "domcontentloaded", timeout: 120000 });
  await installDomCore(page);
}

async function selectModel(page, modelLabel) {
  const raw = String(modelLabel || "").trim();
  if (!raw) return;
  const wanted = raw.toLowerCase()
    .replace(/^(chatgpt|openai)-/, "")
    .replace(/-(pro|extended)$/g, "")
    .replace(/[\s.-]+/g, "");
  if (!wanted) return;
  try {
    await page.bringToFront().catch(() => {});
    const pill = page.locator("button.__composer-pill[aria-haspopup='menu'], button[aria-haspopup='menu']").first();
    await pill.click({ timeout: 4000 });
    await page.locator('[role="menu"], [role="listbox"]').first().waitFor({ state: "visible", timeout: 4000 });
    const items = page.locator('[role="menuitem"], [role="option"]');
    const count = await items.count();
    for (let i = 0; i < count; i++) {
      const item = items.nth(i);
      const text = (await item.innerText({ timeout: 1000 }).catch(() => "")).trim();
      const normalized = text.toLowerCase().replace(/[\s.-]+/g, "");
      if (normalized && (normalized.includes(wanted) || wanted.includes(normalized))) {
        await item.click({ timeout: 4000 });
        log(`selected model ${text}`);
        return;
      }
    }
    await page.keyboard.press("Escape").catch(() => {});
  } catch {
    // Best effort only. ChatGPT often preserves the user's last selected model.
  }
}

async function waitForPromptInput(page, task_id) {
  const input = page.locator("#prompt-textarea, div[contenteditable='true'][role='textbox'], textarea[data-testid='prompt-textarea']").first();
  for (let i = 0; i < 120; i++) {
    try {
      await input.waitFor({ state: "visible", timeout: 1000 });
      return input;
    } catch {
      if (i > 0 && i % 10 === 0) {
        const debug = await page.evaluate(() => window.__automathOracle?.promptDebug?.() || "").catch(() => "");
        await postPhase(task_id, "waiting_prompt_input", debug);
      }
    }
  }
  throw new Error("prompt input not found");
}

async function writeTaskPdfToTemp(task) {
  if (!task.pdf_base64) return null;
  const name = String(task.pdf_name || "paper.pdf").replace(/[<>:"/\\|?*\x00-\x1F]/g, "_");
  const dir = await mkdtemp(path.join(tmpdir(), `automath-${AGENT_ID}-${task.task_id}-`));
  const filePath = path.join(dir, name.toLowerCase().endsWith(".pdf") ? name : `${name}.pdf`);
  await writeFile(filePath, Buffer.from(task.pdf_base64, "base64"));
  return { dir, filePath, href: pathToFileURL(filePath).href };
}

async function waitForUploadComplete(page, task_id) {
  const start = Date.now();
  while (Date.now() - start < UPLOAD_WAIT_MS) {
    await sleep(2000);
    const state = await page.evaluate(() => window.__automathOracle.uploadState()).catch(() => ({}));
    const elapsed = Math.floor((Date.now() - start) / 1000);
    if (!state.uploading && (state.attached || (state.sendEnabled && elapsed > 5))) {
      await postPhase(task_id, "pdf_uploaded", `elapsed=${elapsed}s attached=${!!state.attached}`);
      return true;
    }
    if (elapsed > 0 && elapsed % 10 === 0) {
      await postPhase(task_id, "pdf_upload_wait", `elapsed=${elapsed}s uploading=${!!state.uploading} attached=${!!state.attached}`);
    }
  }
  await postPhase(task_id, "pdf_upload_timeout", "continuing after upload wait timeout");
  return false;
}

async function attachPdfIfPresent(page, task) {
  const pdf_path = task.pdf_path || "";
  if (!task.pdf_base64 && !pdf_path) return null;
  let temp = null;
  let filePath = pdf_path;
  if (task.pdf_base64) {
    temp = await writeTaskPdfToTemp(task);
    filePath = temp.filePath;
  }
  await postPhase(task.task_id, "pdf_uploading", temp ? temp.href : filePath);

  let input = page.locator("input[type='file']").first();
  if ((await input.count()) === 0) {
    // ChatGPT lazy-mounts the hidden file input behind the attach/"+" menu.
    // The UI selectors drift between versions, so try a broad fuzzy set and
    // record which one matched (or that none did) instead of failing silently.
    const attachSelectors = [
      "button[aria-label*='Attach' i]",
      "button[aria-label*='photos and files' i]",
      "button[aria-label*='Upload' i]",
      "button[aria-label*='file' i]",
      "button[data-testid*='attach' i]",
      "button[data-testid*='upload' i]",
      "button[data-testid='composer-plus-btn']",
      "button[aria-haspopup='menu']",
    ];
    let clickedSel = "";
    for (const sel of attachSelectors) {
      const btn = page.locator(sel).first();
      if ((await btn.count()) === 0) continue;
      try {
        await btn.click({ timeout: 4000 });
        clickedSel = sel;
      } catch (e) {
        await postPhase(task.task_id, "pdf_attach_click_fail", `${sel}: ${(e && e.message) || e}`);
        continue;
      }
      await sleep(800);
      // A "+" menu may need a second click on an "Upload from computer" item.
      const menuItem = page.locator(
        "[role='menuitem']:has-text('Upload'), [role='menuitem']:has-text('file'), [role='menuitem']:has-text('computer')"
      ).first();
      if ((await menuItem.count()) > 0) {
        await menuItem.click({ timeout: 3000 }).catch(() => {});
        await sleep(500);
      }
      input = page.locator("input[type='file']").first();
      if ((await input.count()) > 0) break;
    }
    if ((await input.count()) === 0) {
      await postPhase(task.task_id, "pdf_attach_no_input",
        `no file input after ${attachSelectors.length} attach selectors` +
        (clickedSel ? ` (clicked ${clickedSel})` : " (no attach button matched — ChatGPT UI selectors are stale)"));
      console.error(`[pdf] ${task.task_id}: file input not found; attach UI selectors stale`);
    } else if (clickedSel) {
      await postPhase(task.task_id, "pdf_attach_opened", clickedSel);
    }
  }
  if ((await input.count()) === 0) {
    // Surface clearly that this review is going out text-only, then proceed.
    await postPhase(task.task_id, "pdf_upload_failed", "no file input; submitting text-only");
    console.error(`[pdf] ${task.task_id}: PDF NOT attached — review will be text-only`);
    return temp;
  }
  await input.setInputFiles(filePath, { timeout: 30000 });
  await waitForUploadComplete(page, task.task_id);
  await sleep(5000);
  return temp;
}

async function fillPrompt(input, prompt) {
  await input.click();
  await input.fill(prompt || "");
}

async function clickSend(page) {
  const sendButton = page.locator("button[data-testid='send-button'], button[aria-label='Send prompt'], button[aria-label='Send message']").first();
  await sendButton.click({ timeout: 30000 });
}

async function waitForResponse(page, task_id, beforeCount) {
  const start = Date.now();
  let lastHeartbeat = start;
  let lastKey = "";
  let stable = 0;

  while (Date.now() - start < MAX_WAIT_MS) {
    await sleep(STABLE_INTERVAL_MS);
    if (Date.now() - lastHeartbeat >= HEARTBEAT_MS) {
      lastHeartbeat = Date.now();
      await postPhase(task_id, "waiting_response", `${Math.floor((Date.now() - start) / 1000)}s`);
    }

    const [generating, count, text] = await page.evaluate(() => [
      window.__automathOracle.isStillGenerating(),
      window.__automathOracle.assistantCount(),
      window.__automathOracle.extractResponse(),
    ]);

    if (count <= beforeCount) continue;
    if (generating) {
      stable = 0;
      continue;
    }

    const key = `${(text || "").slice(0, 200)}|${(text || "").length}`;
    if (key === lastKey && text && text.trim()) {
      stable += 1;
      if (stable >= 2) return text;
    } else {
      stable = 0;
      lastKey = key;
    }
  }

  const [count, text] = await page.evaluate(() => [
    window.__automathOracle.assistantCount(),
    window.__automathOracle.extractResponse(),
  ]);
  return count > beforeCount ? text : "";
}

async function handlePrompt(page, task) {
  const task_id = task.task_id;
  let temp = null;
  try {
    await page.bringToFront().catch(() => {});
    await navigateForTask(page, task);
    await installDomCore(page);

    const input = await waitForPromptInput(page, task_id);
    await ack(task_id, "page_ready");
    await postPhase(task_id, "prompt_ready", `model=${task.model || ""}`);

    await selectModel(page, task.model);
    temp = await attachPdfIfPresent(page, task);

    const beforeCount = await page.evaluate(() => window.__automathOracle.assistantCount());
    await fillPrompt(input, task.prompt || "");
    await postPhase(task_id, "prompt_inserted", `chars=${String(task.prompt || "").length}`);
    await clickSend(page);
    await ack(task_id, "sent");

    await sleep(3000);
    await pinConversationUrl(task, page);
    const response = await waitForResponse(page, task_id, beforeCount);
    await pinConversationUrl(task, page);

    if (!response || !response.trim()) {
      await postResult(task, "ERROR: empty extraction", page);
      log(`task ${task_id} -> empty extraction`);
      return;
    }
    const result = await postResult(task, response, page);
    log(`task ${task_id} -> ${result.status} (${response.length} chars)`);
  } finally {
    if (temp?.dir) {
      await rm(temp.dir, { recursive: true, force: true }).catch(() => {});
    }
  }
}

async function main() {
  log(`connecting to Chrome at ${CDP_URL}`);
  const browser = await chromium.connectOverCDP(CDP_URL);
  const context = browser.contexts()[0] || await browser.newContext();
  let page = await getChatPage(context, AGENT_ID);
  log(`attached. base=${BASE_URL} agent=${AGENT_ID}. polling...`);

  for (;;) {
    try {
      if (page.isClosed()) page = await getChatPage(context, AGENT_ID);
      const task = await apiGet(`/task?agent=${enc(AGENT_ID)}&script_version=${enc(SCRIPT_VERSION)}&page_url=${enc(page.url())}`);
      if (task.status === "busy") {
        log(`assigned_agent busy: ${task.assigned_agent || AGENT_ID}`);
      } else if (task.task_id) {
        log(`task ${task.task_id} prompt=${String(task.prompt || "").length} pdf=${!!task.pdf_base64 || !!task.pdf_path}`);
        try {
          await handlePrompt(page, task);
        } catch (err) {
          log(`task ${task.task_id} errored: ${err.message}`);
          try {
            await postResult(task, `ERROR: ${err.message}`, page);
          } catch {
            await releaseTask(task, `cdp_worker_error: ${err.message}`);
          }
        }
      }
    } catch (err) {
      log(`poll error: ${err.message}`);
    }
    await sleep(POLL_MS);
  }
}

main().catch((err) => {
  console.error("fatal:", err);
  process.exit(1);
});
