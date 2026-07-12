#!/usr/bin/env node
// NyxID Oracle CDP worker.
//
// A lower-friction alternative to the Tampermonkey userscript: instead of
// installing a userscript and babysitting a tab, this attaches to your
// already-running, already-logged-in Chrome over the DevTools Protocol and
// drives the ChatGPT tab for you. Same NyxID worker API, same proven answer
// extraction — but no extension to install and it runs as a background daemon.
//
// Because it drives your REAL Chrome (real session, real TLS fingerprint, the
// Cloudflare clearance you already earned by logging in normally), it is far
// less bot-detectable than a fresh headless browser.
//
// Setup (two commands — see README.md):
//   1. Launch Chrome with a debug port (and your normal profile, logged into
//      ChatGPT):
//        "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
//          --remote-debugging-port=9222 --user-data-dir="$HOME/.nyxid-chrome"
//   2. Run this worker:
//        NYXID_BASE_URL=https://auth.nyxid.dev \
//        NYXID_WORKER_TOKEN=nyx_owk_... \
//        node worker.mjs
//
// Requires: Node 18+ (built-in fetch) and `npm i` (playwright-core only).

import { chromium } from "playwright-core";
import { ProxyAgent, setGlobalDispatcher } from "undici";
import { lookup } from "node:dns/promises";
import { isIP } from "node:net";
import { readFileSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import {
  boundedBackoffMs,
  conversationId,
  normalizeModelRequest,
  resolveTaskMode,
  safeArtifactName,
} from "./policy.mjs";

const BASE_URL = (process.env.NYXID_BASE_URL || "").replace(/\/$/, "");
// Prefer a token file (NYXID_WORKER_TOKEN_FILE) so the long-lived worker token
// stays out of shell history and the process environment (`ps e`,
// /proc/<pid>/environ). Falls back to NYXID_WORKER_TOKEN for convenience.
const TOKEN = (() => {
  const file = process.env.NYXID_WORKER_TOKEN_FILE;
  if (file) return readFileSync(file, "utf8").trim();
  return process.env.NYXID_WORKER_TOKEN || "";
})();
const LABEL = process.env.NYXID_WORKER_LABEL || "tab_1";
const CDP_URL = process.env.CHROME_CDP_URL || "http://localhost:9222";
const TAB_URL_MATCH = process.env.NYXID_CHATGPT_TAB_URL_MATCH || "";
const TAB_STORAGE_MARKER = process.env.NYXID_CHATGPT_TAB_STORAGE_MARKER || "";
const SCRIPT_VERSION = process.env.NYXID_WORKER_SCRIPT_VERSION || "cdp-2.0-chat-work";
const POLL_MS = Number(process.env.NYXID_POLL_MS || 5000);
const STABLE_INTERVAL_MS = 8000;
const MAX_WAIT_MS = Number(process.env.NYXID_MAX_WAIT_MS || 2 * 60 * 60 * 1000); // 2h
const HEARTBEAT_MS = 60000;
const FETCH_PROXY = process.env.NYXID_FETCH_PROXY || process.env.HTTPS_PROXY || process.env.HTTP_PROXY || "";
const STATE_DIR = process.env.NYXID_STATE_DIR || path.resolve(process.cwd(), ".nyxid-oracle");
const MAX_ARTIFACT_BYTES = Number(process.env.NYXID_MAX_ARTIFACT_BYTES || 20 * 1024 * 1024);
const MAX_ARTIFACT_TOTAL_BYTES = Number(process.env.NYXID_MAX_ARTIFACT_TOTAL_BYTES || 50 * 1024 * 1024);

if (FETCH_PROXY) {
  setGlobalDispatcher(new ProxyAgent(FETCH_PROXY));
}

if (!BASE_URL || !TOKEN) {
  console.error(
    "Missing config. Set NYXID_BASE_URL and the pool worker token (nyx_owk_...) " +
      "via NYXID_WORKER_TOKEN_FILE (preferred) or NYXID_WORKER_TOKEN."
  );
  process.exit(1);
}

const API = `${BASE_URL}/api/v1/oracle/worker`;

function log(msg) {
  console.log(`[nyxid-cdp ${new Date().toISOString()}] ${msg}`);
}
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ── NyxID worker API (Bearer worker token) ───────────────────────────────
function httpError(method, path, status) {
  const err = new Error(`${method} ${path} → ${status}`);
  err.status = status;
  return err;
}
async function apiGet(path) {
  const res = await fetch(`${API}${path}`, {
    headers: { Authorization: `Bearer ${TOKEN}` },
  });
  if (!res.ok) throw httpError("GET", path, res.status);
  return res.json();
}
async function apiPost(path, body) {
  const res = await fetch(`${API}${path}`, {
    method: "POST",
    headers: {
      Authorization: `Bearer ${TOKEN}`,
      "Content-Type": "application/json",
    },
    body: JSON.stringify({ ...body, script_version: SCRIPT_VERSION }),
  });
  if (!res.ok) throw httpError("POST", path, res.status);
  return res.json();
}

// ── SSRF defense for `extract` (defense-in-depth with the server-side
// `validate_extract_url` guard) ──────────────────────────────────────────
// The server authoritatively rejects loopback/private/link-local/metadata
// targets, but it can't see DNS-rebinding (a public name that resolves to a
// private address). The worker drives the operator's REAL logged-in Chrome,
// so re-validate here at navigation time: resolve the host and refuse any
// non-public address. Best-effort (a TOCTOU window remains before goto), but
// it closes the rebinding gap the server cannot.
function isBlockedIp(ip) {
  const v = isIP(ip);
  if (v === 4) {
    const o = ip.split(".").map(Number);
    if (o[0] === 10) return true; // 10/8 private
    if (o[0] === 127) return true; // loopback
    if (o[0] === 0) return true; // unspecified / this-network
    if (o[0] === 169 && o[1] === 254) return true; // link-local + metadata
    if (o[0] === 172 && o[1] >= 16 && o[1] <= 31) return true; // 172.16/12
    if (o[0] === 192 && o[1] === 168) return true; // 192.168/16
    if (o[0] === 100 && o[1] >= 64 && o[1] <= 127) return true; // 100.64/10 CGNAT
    if (o[0] >= 224) return true; // multicast + reserved + broadcast
    return false;
  }
  if (v === 6) {
    const a = ip.toLowerCase();
    if (a === "::" || a === "::1") return true; // unspecified / loopback
    const head = a.split(":")[0] || "";
    const b0 = parseInt(head.padStart(4, "0").slice(0, 2), 16);
    if ((b0 & 0xfe) === 0xfc) return true; // fc00::/7 unique-local
    if (b0 === 0xfe) {
      const b1 = parseInt(head.padStart(4, "0").slice(2, 4), 16);
      if ((b1 & 0xc0) === 0x80) return true; // fe80::/10 link-local
    }
    if (a.startsWith("ff")) return true; // multicast
    // IPv4-mapped ::ffff:a.b.c.d — re-check the embedded v4.
    const m = a.match(/::ffff:(\d+\.\d+\.\d+\.\d+)$/);
    if (m) return isBlockedIp(m[1]);
    return false;
  }
  return true; // not a recognizable IP → refuse
}
async function assertPublicTarget(rawUrl) {
  let u;
  try {
    u = new URL(rawUrl);
  } catch {
    throw new Error("invalid extract url");
  }
  if (u.protocol !== "http:" && u.protocol !== "https:") {
    throw new Error("extract url scheme not allowed");
  }
  const host = u.hostname.replace(/^\[|\]$/g, "");
  if (isIP(host)) {
    if (isBlockedIp(host)) throw new Error("extract target host is not allowed");
    return;
  }
  const addrs = await lookup(host, { all: true });
  if (!addrs.length) throw new Error("extract host did not resolve");
  for (const { address } of addrs) {
    if (isBlockedIp(address)) {
      throw new Error("extract target resolves to a non-public address");
    }
  }
}

// ── DOM core injected into the ChatGPT page ──────────────────────────────
// Ported from the proven userscript extractors: KaTeX/MathJax → LaTeX, the
// Pro-reasoning "still generating" probe, latest-answer + full-transcript
// extraction. Installed on window.__nyx and re-installed after navigation.
const DOM_CORE = `
window.__nyx = (function () {
  function extractTextWithMath(el) {
    if (!el) return "";
    const clone = el.cloneNode(true);
    for (const ann of Array.from(clone.querySelectorAll('annotation[encoding="application/x-tex"]'))) {
      const latex = (ann.textContent || "").trim();
      if (!latex) continue;
      const outer = ann.closest(".katex-display, .katex") || ann.parentElement;
      if (outer) {
        const disp = outer.classList.contains("katex-display") ||
          (outer.parentElement && outer.parentElement.classList.contains("katex-display"));
        outer.replaceWith(document.createTextNode(disp ? "\\n$$" + latex + "$$\\n" : " $" + latex + "$ "));
      }
    }
    for (const mjx of Array.from(clone.querySelectorAll("mjx-container"))) {
      let latex = "";
      const a = mjx.querySelector('annotation[encoding*="TeX"]');
      if (a) latex = (a.textContent || "").trim();
      if (!latex) latex = mjx.getAttribute("aria-label") || mjx.getAttribute("data-latex") || "";
      if (latex) {
        const disp = mjx.getAttribute("display") === "true" || mjx.getAttribute("data-display") === "block";
        mjx.replaceWith(document.createTextNode(disp ? "\\n$$" + latex + "$$\\n" : " $" + latex + "$ "));
      }
    }
    for (const m of Array.from(clone.querySelectorAll("math"))) {
      const alt = m.getAttribute("alttext") || "";
      if (alt) m.replaceWith(document.createTextNode(" $" + alt + "$ "));
    }
    return (clone.innerText || "").trim();
  }

  const CHROME_RE = /^(ChatGPT|You said:|ChatGPT said:|Copy code|Copy|Share|Regenerate|4o|o\\d|GPT-|Ask anything|Send a message)$/i;
  const REASONING_RE = /^(Thought for\\s+\\d+|Thinking|Reasoning|Pro thinking|Extended Pro|Show less|Show more|显示更多|显示较少)$/i;
  function cleanText(text) {
    return text.split("\\n").filter((line) => {
      const t = line.trim();
      if (!t) return true;
      if (CHROME_RE.test(t)) return false;
      if (REASONING_RE.test(t)) return false;
      return true;
    }).join("\\n").trim();
  }

  function isReasoningBlock(el) {
    if (!el) return false;
    const attr = [
      el.getAttribute("data-testid"),
      el.getAttribute("aria-label"),
      el.getAttribute("data-message-author-role"),
      el.className,
    ].join(" ");
    if (/reason|think|thought|思考/i.test(attr)) return true;
    const text = (el.innerText || el.textContent || "").trim();
    if (!text) return false;
    if (/^(Thought for\\s+\\d+|Thinking|Reasoning|Pro thinking|Extended Pro|Show less|Show more)/i.test(text)) return true;
    return false;
  }

  function messageContentCandidates(assistantEl) {
    if (!assistantEl) return [];
    const selectors = [
      "[data-message-author-role='assistant'] [data-testid*='message']",
      "[data-message-author-role='assistant'] [data-testid*='conversation-turn'] .markdown",
      "[data-message-author-role='assistant'] .markdown",
      "[data-message-author-role='assistant'] .prose",
      "[data-message-id]",
      ".markdown",
      ".prose",
    ];
    const candidates = [];
    const seen = new Set();
    for (const selector of selectors) {
      for (const el of Array.from(assistantEl.querySelectorAll(selector))) {
        if (seen.has(el)) continue;
        seen.add(el);
        if (isReasoningBlock(el) || el.closest("[data-testid*='reasoning'], [class*='reasoning'], [class*='thinking']")) continue;
        const text = cleanText(extractTextWithMath(el));
        if (!text) continue;
        candidates.push({ el, text });
      }
    }
    if (!candidates.length && !isReasoningBlock(assistantEl)) {
      const text = cleanText(extractTextWithMath(assistantEl));
      if (text) candidates.push({ el: assistantEl, text });
    }
    return candidates;
  }

  function extractAssistantContent(assistantEl) {
    const candidates = messageContentCandidates(assistantEl);
    if (!candidates.length) return "";
    candidates.sort((a, b) => b.text.length - a.text.length);
    return candidates[0].text;
  }

  function isStillGenerating() {
    const dom = !!(
      document.querySelector("button[aria-label='Stop generating']") ||
      document.querySelector("button[aria-label='Stop streaming']") ||
      document.querySelector("button[aria-label='停止生成']") ||
      document.querySelector("button[data-testid='stop-button']") ||
      document.querySelector("[class*='result-streaming']") ||
      document.querySelector("[class*='streaming']") ||
      document.querySelector("[class*='thinking']") ||
      document.querySelector("[class*='reasoning']")
    );
    if (dom) return true;
    try {
      const main = document.querySelector("main");
      if (!main) return false;
      const txt = main.innerText || "";
      const pre = /Pro thinking|Extended Pro|Reasoning…/i.test(txt);
      const post = /Thought for\\s+\\d+/i.test(txt);
      if (pre && !post) return true;
    } catch (e) {}
    return false;
  }

  function assistantCount() {
    return document.querySelectorAll("[data-message-author-role='assistant']").length;
  }

  function scrollContainer() {
    const firstMessage = document.querySelector("[data-message-author-role]");
    let el = firstMessage ? firstMessage.parentElement : null;
    while (el && el !== document.body && el !== document.documentElement) {
      try {
        const style = getComputedStyle(el);
        if (
          el.scrollHeight > el.clientHeight + 4 &&
          (style.overflowY === "auto" || style.overflowY === "scroll")
        ) {
          return el;
        }
      } catch (e) {}
      el = el.parentElement;
    }
    return document.scrollingElement || document.body;
  }

  // Latest assistant message text (the answer to the last prompt).
  function extractResponse() {
    const main = document.querySelector("main");
    if (!main) return "";
    const els = main.querySelectorAll("[data-testid^='conversation-turn'] [data-message-author-role='assistant'], [data-message-author-role='assistant']");
    if (!els.length) return "";
    for (let i = els.length - 1; i >= 0; i--) {
      const text = extractAssistantContent(els[i]);
      if (text) return text;
    }
    return "";
  }

  // Full conversation: every user/assistant turn in order.
  function extractTranscript() {
    const main = document.querySelector("main") || document.body;
    const nodes = main.querySelectorAll("[data-message-author-role]");
    const turns = [];
    for (const el of nodes) {
      const role = el.getAttribute("data-message-author-role");
      if (role !== "user" && role !== "assistant") continue;
      const text = role === "assistant" ? extractAssistantContent(el) : cleanText(extractTextWithMath(el));
      if (text) turns.push({ role, text });
    }
    return turns;
  }

  function extractTranscriptKeys() {
    const main = document.querySelector("main") || document.body;
    const nodes = Array.from(main.querySelectorAll("[data-message-author-role]"));
    const turns = [];
    let fallbackIndex = 0;
    for (const el of nodes) {
      const role = el.getAttribute("data-message-author-role");
      if (role !== "user" && role !== "assistant") continue;
      const turn = el.closest('[data-testid^="conversation-turn"]');
      const testid = turn ? turn.getAttribute("data-testid") : "";
      let key = testid || role + "#" + fallbackIndex++;
      const text = role === "assistant" ? extractAssistantContent(el) : cleanText(extractTextWithMath(el));
      if (!text) continue;
      if (!testid) key = key + "|" + text;
      turns.push({ key, role, text });
    }
    return { rendered: nodes.length, turns };
  }

  return { isStillGenerating, assistantCount, extractResponse, extractTranscript, extractTranscriptKeys, scrollContainer, extractTextWithMath, cleanText, extractAssistantContent };
})();
`;

async function installDomCore(page) {
  // applies on future navigations…
  await page.addInitScript({ content: DOM_CORE });
  // …and right now.
  try {
    await page.evaluate(DOM_CORE);
  } catch (e) {
    /* page mid-navigation; addInitScript covers the next load */
  }
}

// ── ChatGPT tab acquisition ──────────────────────────────────────────────
function isChatGptUrl(u) {
  return /https:\/\/(chatgpt\.com|chat\.openai\.com)\//.test(u || "");
}

async function pageHasStorageMarker(page) {
  if (!TAB_STORAGE_MARKER) return true;
  try {
    return await page.evaluate((marker) => {
      const keys = [
        "NYXID_CHATGPT_TAB_STORAGE_MARKER",
        "nyxid_chatgpt_tab_storage_marker",
        "nyxid_oracle_marker",
      ];
      for (const key of keys) {
        if (sessionStorage.getItem(key) === marker) return true;
      }
      return false;
    }, TAB_STORAGE_MARKER);
  } catch (e) {
    return false;
  }
}

async function markCompanyTab(page) {
  if (!TAB_STORAGE_MARKER) return;
  await page.evaluate((marker) => {
    sessionStorage.setItem("NYXID_CHATGPT_TAB_STORAGE_MARKER", marker);
    sessionStorage.setItem("nyxid_chatgpt_tab_storage_marker", marker);
    sessionStorage.setItem("nyxid_oracle_marker", marker);
  }, TAB_STORAGE_MARKER);
}

async function matchesConfiguredTab(page) {
  const url = page.url();
  if (!isChatGptUrl(url)) return false;
  if (!TAB_URL_MATCH) return pageHasStorageMarker(page);
  return url.includes(TAB_URL_MATCH) || await pageHasStorageMarker(page);
}

async function getChatPage(context) {
  let page = null;
  for (const candidate of context.pages()) {
    if (await matchesConfiguredTab(candidate)) {
      page = candidate;
      break;
    }
  }
  if (!page) {
    page = await context.newPage();
    const suffix = TAB_URL_MATCH ? `?${TAB_URL_MATCH}` : "";
    await page.goto(`https://chatgpt.com/${suffix}`, { waitUntil: "domcontentloaded" });
    await markCompanyTab(page);
  } else {
    await markCompanyTab(page);
  }
  await installDomCore(page);
  return page;
}

// ── Prompt flow ──────────────────────────────────────────────────────────
function normalizeModelLabel(label) {
  return (label || "")
    .toLowerCase()
    .trim()
    .replace(/^(chatgpt|openai)-/, "")
    .replace(/-(pro|extended)$/g, "")
    .replace(/[\s.-]+/g, "");
}

async function clickFirstVisible(locator, timeout = 5000) {
  const count = await locator.count();
  for (let i = 0; i < count; i++) {
    const item = locator.nth(i);
    try {
      await item.click({ timeout });
      return true;
    } catch (e) {}
  }
  return false;
}

async function waitForModelMenu(page, timeout = 5000) {
  try {
    await page.locator('[role="menu"], [role="listbox"]').first().waitFor({ state: "visible", timeout });
    return true;
  } catch (e) {
    return false;
  }
}

async function clickMatchingModelItem(page, wanted) {
  const items = page.locator('[role="menuitem"], [role="option"]');
  const count = await items.count();
  for (let i = 0; i < count; i++) {
    const item = items.nth(i);
    let text = "";
    try {
      if (!(await item.isVisible())) continue;
      text = (await item.innerText({ timeout: 1000 })).trim();
    } catch (e) {
      continue;
    }
    const candidate = normalizeModelLabel(text);
    if (!candidate) continue;
    if (candidate.includes(wanted) || wanted.includes(candidate)) {
      await item.click({ timeout: 5000 });
      return text || candidate;
    }
  }
  return null;
}

async function selectModel(page, modelLabel) {
  try {
    await page.bringToFront().catch(() => {});
    const rawLabel = (modelLabel || "").trim();
    const wanted = normalizeModelLabel(rawLabel);
    if (!wanted) return;

    const target = await page.evaluate((label) => {
      const raw = (label || "").trim();
      const lower = raw.toLowerCase();
      const compact = lower
        .replace(/^(chatgpt|openai)-/, "")
        .replace(/[\s._-]+/g, "");
      if (lower.includes("pro")) return "Pro 扩展";
      if (/极速|fast/.test(lower)) return "极速";
      if (/均衡|balanced/.test(lower)) return "均衡";
      if (/高级|advanced/.test(lower)) return "高级";
      if (/超高|ultra/.test(lower)) return "超高";
      if (/扩展|extended/.test(lower)) return "Pro 扩展";
      if (/gpt[\s-]*5(\.5)?\b/.test(lower) || /\b5\.5\b/.test(lower) || compact === "gpt55" || compact === "gpt5") {
        return "GPT-5.5";
      }
      return raw;
    }, rawLabel);

    log(`selecting model "${modelLabel}"`);
    const opened = await page.evaluate(() => {
      try {
        const visible = (el) => {
          const r = el.getBoundingClientRect();
          const style = getComputedStyle(el);
          return r.width > 0 && r.height > 0 && style.visibility !== "hidden" && style.display !== "none";
        };
        let picker = document.querySelector('button.__composer-pill[aria-haspopup="menu"]');
        if (!picker || !visible(picker)) {
          picker = Array.from(document.querySelectorAll('button[aria-haspopup="menu"]')).find((btn) => {
            if (!visible(btn)) return false;
            const text = (btn.innerText || btn.textContent || "").trim();
            return text.length > 0 &&
              text.length < 30 &&
              /pro|gpt|思考|扩展|极速|均衡|高级|超高|\b5(\.|\b)/i.test(text);
          });
        }
        if (!picker) return false;
        picker.click();
        return true;
      } catch (e) {
        return false;
      }
    });

    if (!opened || !(await waitForModelMenu(page, 5000))) {
      log(`model picker unavailable for "${modelLabel}", using current`);
      return;
    }

    const clickMatch = async () => page.evaluate(({ label, resolvedTarget }) => {
      try {
        const normalize = (value) => (value || "")
          .toLowerCase()
          .trim()
          .replace(/^(chatgpt|openai)-/, "")
          .replace(/[\s._-]+/g, "");
        const rawNeedle = (label || "").trim();
        const rawTarget = (resolvedTarget || "").trim();
        const wantedValues = Array.from(new Set([
          normalize(rawNeedle),
          normalize(rawTarget),
        ].filter(Boolean)));
        const directValues = [rawNeedle.toLowerCase(), rawTarget.toLowerCase()].filter(Boolean);
        const visible = (el) => {
          const r = el.getBoundingClientRect();
          const style = getComputedStyle(el);
          return r.width > 0 && r.height > 0 && style.visibility !== "hidden" && style.display !== "none";
        };
        const items = Array.from(document.querySelectorAll('[role="menuitemradio"],[role="menuitem"],[role="option"]'));
        for (const item of items) {
          if (!visible(item)) continue;
          const text = (item.innerText || item.textContent || "").trim();
          if (!text) continue;
          const candidate = normalize(text);
          const direct = text.toLowerCase();
          const matched = wantedValues.some((wanted) => candidate === wanted || candidate.includes(wanted) || wanted.includes(candidate)) ||
            directValues.some((wanted) => direct === wanted || direct.includes(wanted) || wanted.includes(direct));
          if (!matched) continue;
          const role = item.getAttribute("role") || "";
          item.click();
          return { text, role };
        }
      } catch (e) {}
      return null;
    }, { label: rawLabel, resolvedTarget: target });

    let directMatch = await clickMatch();
    if (directMatch && directMatch.role === "menuitem" && normalizeModelLabel(target) === "gpt55") {
      await sleep(600);
      directMatch = (await clickMatch()) || directMatch;
    }
    if (directMatch) {
      log(`model set to "${target}"`);
      return;
    }

    const openedEffortSubmenu = await page.evaluate(() => {
      try {
        const trigger = document.querySelector('[data-testid="composer-intelligence-pro-thinking-effort-trigger"]');
        if (!trigger) return false;
        trigger.click();
        return true;
      } catch (e) {
        return false;
      }
    });
    if (openedEffortSubmenu) {
      await sleep(600);
      directMatch = await clickMatch();
      if (directMatch) {
        log(`model set to "${target}"`);
        return;
      }
    }

    await page.keyboard.press("Escape");
    log(`model "${modelLabel}" not found in picker, using current`);
  } catch (err) {
    try {
      await page.keyboard.press("Escape");
    } catch (e) {}
    log(`model "${modelLabel}" selection failed: ${err.message}; using current`);
  }
}

async function selectAndVerifyMode(page, mode) {
  const modeLabel = mode === "work" ? "Work" : "Chat";
  const radio = page.getByRole("radio", { name: modeLabel, exact: true });
  await radio.waitFor({ state: "visible", timeout: 30000 });
  if ((await radio.getAttribute("data-state")) !== "on") {
    await radio.click({ timeout: 10000 });
    await page.waitForTimeout(500);
  }
  const state = await page.getByRole("radio", { name: modeLabel, exact: true }).getAttribute("data-state");
  if (state !== "on") throw new Error(`ChatGPT ${modeLabel} mode did not become active`);
  return mode;
}

async function chooseModelMenuValue(page, groupName, requestedValue) {
  if (!requestedValue) return "";
  const menu = page.locator('[role="menu"]').last();
  const trigger = menu.getByRole("menuitem").filter({ hasText: new RegExp(`^${groupName}\\b`, "i") }).first();
  await trigger.click({ timeout: 7000 });
  await page.waitForTimeout(350);
  const choices = page.locator('[role="menuitemradio"], [role="menuitem"], [role="option"]');
  const wanted = normalizeModelLabel(requestedValue);
  const count = await choices.count();
  for (let i = 0; i < count; i++) {
    const choice = choices.nth(i);
    if (!(await choice.isVisible().catch(() => false))) continue;
    const text = (await choice.innerText().catch(() => "")).trim();
    const candidate = normalizeModelLabel(text);
    if (!candidate || !(candidate === wanted || candidate.includes(wanted) || wanted.includes(candidate))) continue;
    await choice.click({ timeout: 7000 });
    await page.waitForTimeout(350);
    return text;
  }
  throw new Error(`${groupName} option not found: ${requestedValue}`);
}

async function configureModel(page, task) {
  const requested = normalizeModelRequest(task);
  if (!requested.model && !requested.effort && !requested.speed && !requested.power) return {};
  const picker = page.locator("button.__composer-pill").first();
  await picker.waitFor({ state: "visible", timeout: 30000 });
  await picker.click({ timeout: 7000 });
  await page.locator('[role="menu"]').last().waitFor({ state: "visible", timeout: 7000 });

  const observed = {};
  try {
    if (requested.power) {
      const slider = page.locator('[role="slider"]').first();
      if ((await slider.count()) === 0) throw new Error("Power slider not found");
      await slider.focus();
      await page.keyboard.press("Home");
      for (let i = 1; i < requested.power; i++) await page.keyboard.press("ArrowRight");
      observed.power = requested.power;
    }
    if (requested.model) observed.model = await chooseModelMenuValue(page, "Model", requested.model);
    if (requested.effort) {
      if (!(await page.locator('[role="menu"]').last().isVisible().catch(() => false))) await picker.click();
      observed.effort = await chooseModelMenuValue(page, "Effort", requested.effort);
    }
    if (requested.speed) {
      if (!(await page.locator('[role="menu"]').last().isVisible().catch(() => false))) await picker.click();
      observed.speed = await chooseModelMenuValue(page, "Speed", requested.speed);
    }
  } finally {
    await page.keyboard.press("Escape").catch(() => {});
  }
  return observed;
}

async function detectConversationMode(page) {
  const isWork = await page.evaluate(() => {
    const header = document.querySelector("#page-header");
    if (header && Array.from(header.querySelectorAll("span")).some((el) => (el.textContent || "").trim() === "Work")) return true;
    const text = header ? (header.innerText || "") : "";
    return /\bProgress\b/.test(text) && /\bOutputs\b/.test(text) && /\bSubagents\b/.test(text);
  });
  return isWork ? "work" : "chat";
}

async function verifyFollowupConversation(page, task) {
  const expected = conversationId(task.conversation_url);
  if (!expected) throw new Error("follow-up requires a valid ChatGPT conversation_url");
  await page.goto(task.conversation_url, { waitUntil: "domcontentloaded", timeout: 120000 });
  await installDomCore(page);
  await page.locator("#prompt-textarea, [contenteditable='true'][role='textbox']").first()
    .waitFor({ state: "visible", timeout: 60000 });
  const actual = conversationId(page.url());
  if (actual !== expected) throw new Error(`follow-up conversation mismatch: expected ${expected}, got ${actual || "none"}`);
  return detectConversationMode(page);
}

function taskFiles(task) {
  const files = Array.isArray(task.files) ? [...task.files] : [];
  if (task.pdf_base64) {
    files.push({
      name: task.pdf_name || "paper.pdf",
      mime_type: "application/pdf",
      content_base64: task.pdf_base64,
    });
  }
  return files.filter((file) => file && file.content_base64);
}

async function prepareTaskFiles(task) {
  const files = taskFiles(task);
  if (!files.length) return null;
  const dir = await mkdtemp(path.join(tmpdir(), `nyxid-${LABEL}-${task.task_id}-`));
  const paths = [];
  for (let i = 0; i < files.length; i++) {
    const file = files[i];
    const name = safeArtifactName(file.name, i + 1, file.mime_type);
    const filePath = path.join(dir, name);
    await writeFile(filePath, Buffer.from(file.content_base64, "base64"));
    paths.push(filePath);
  }
  return { dir, paths };
}

async function uploadTaskFiles(page, task, prepared) {
  if (!prepared?.paths.length) return;
  let inputs = page.locator("input[type='file']");
  if ((await inputs.count()) === 0) {
    await page.locator("button[data-testid='composer-plus-btn']").first().click({ timeout: 10000 });
    const upload = page.getByText("Upload from computer", { exact: true }).last();
    await upload.click({ timeout: 10000 }).catch(() => {});
    await page.waitForTimeout(400);
    inputs = page.locator("input[type='file']");
  }
  let uploaded = false;
  for (let i = 0; i < await inputs.count(); i++) {
    try {
      await inputs.nth(i).setInputFiles(prepared.paths, { timeout: 15000 });
      uploaded = true;
      break;
    } catch {}
  }
  if (!uploaded) throw new Error("file_input_missing: no ChatGPT file input accepted the task files");

  const send = page.locator("button[data-testid='send-button']").first();
  const deadline = Date.now() + 90000;
  while (Date.now() < deadline) {
    const uploading = await page.locator("[role='progressbar'], [class*='uploading']").count();
    if (!uploading && await send.isEnabled().catch(() => false)) return;
    await page.waitForTimeout(1000);
  }
  throw new Error(`upload_timeout: ${taskFiles(task).length} attachment(s) did not settle`);
}

async function downloadArtifact(context, page, candidate, index) {
  let bytes;
  if (candidate.url.startsWith("blob:")) {
    const base64 = await page.evaluate(async (url) => {
      const response = await fetch(url);
      const blob = await response.blob();
      return new Promise((resolve, reject) => {
        const reader = new FileReader();
        reader.onload = () => resolve(String(reader.result).split(",")[1] || "");
        reader.onerror = reject;
        reader.readAsDataURL(blob);
      });
    }, candidate.url);
    bytes = Buffer.from(base64, "base64");
  } else {
    const response = await context.request.get(candidate.url, { timeout: 30000 });
    if (!response.ok()) throw new Error(`artifact download returned ${response.status()}`);
    bytes = await response.body();
  }
  if (bytes.length > MAX_ARTIFACT_BYTES) throw new Error(`artifact exceeds ${MAX_ARTIFACT_BYTES} bytes`);
  const mimeType = candidate.mime_type || "application/octet-stream";
  return {
    name: safeArtifactName(candidate.name, index, mimeType),
    mime_type: mimeType,
    source: candidate.source,
    source_url: candidate.url,
    content_base64: bytes.toString("base64"),
    width: candidate.width || null,
    height: candidate.height || null,
  };
}

async function collectArtifacts(context, page) {
  const candidates = await page.evaluate(() => {
    const visible = (el) => {
      const rect = el.getBoundingClientRect();
      return rect.width > 0 && rect.height > 0;
    };
    const finalTurn = Array.from(document.querySelectorAll("[data-testid^='conversation-turn']"))
      .filter((turn) => turn.querySelector("[data-message-author-role='assistant']")).at(-1);
    const outputRoots = Array.from(document.querySelectorAll("#page-header, [data-testid*='output'], [aria-label*='Output' i]"));
    const roots = [finalTurn, ...outputRoots].filter(Boolean);
    const seen = new Set();
    const found = [];
    for (const root of roots) {
      for (const el of root.querySelectorAll("img[src], a[download], a[href]")) {
        if (!visible(el)) continue;
        const url = el.currentSrc || el.src || el.href || "";
        if (!url || seen.has(url) || /favicon|avatar|emoji/i.test(url)) continue;
        const looksDownload = el.tagName === "IMG" || el.hasAttribute("download") || /\.(png|jpe?g|webp|gif|svg|pdf)(\?|$)/i.test(url);
        if (!looksDownload) continue;
        seen.add(url);
        found.push({
          url,
          name: el.getAttribute("download") || el.getAttribute("alt") || "",
          mime_type: el.tagName === "IMG" ? "image/png" : "application/octet-stream",
          source: outputRoots.some((output) => output.contains(el)) ? "work_output" : "answer",
          width: el.naturalWidth || null,
          height: el.naturalHeight || null,
        });
      }
    }
    return found.slice(0, 20);
  });

  const artifacts = [];
  const errors = [];
  let total = 0;
  for (let i = 0; i < candidates.length; i++) {
    try {
      const artifact = await downloadArtifact(context, page, candidates[i], i + 1);
      const size = Buffer.byteLength(artifact.content_base64, "base64");
      if (total + size > MAX_ARTIFACT_TOTAL_BYTES) throw new Error(`artifact total exceeds ${MAX_ARTIFACT_TOTAL_BYTES} bytes`);
      total += size;
      artifacts.push(artifact);
    } catch (error) {
      errors.push({ source_url: candidates[i].url, error: error.message });
    }
  }
  return { artifacts, errors };
}

async function spoolArtifacts(taskId, artifacts, errors) {
  const dir = path.join(STATE_DIR, "artifact-spool", String(taskId));
  await mkdir(dir, { recursive: true });
  const manifest = [];
  for (let i = 0; i < artifacts.length; i++) {
    const artifact = artifacts[i];
    const filePath = path.join(dir, safeArtifactName(artifact.name, i + 1, artifact.mime_type));
    await writeFile(filePath, Buffer.from(artifact.content_base64, "base64"));
    manifest.push({ ...artifact, content_base64: undefined, file: filePath });
  }
  await writeFile(path.join(dir, "manifest.json"), JSON.stringify({ artifacts: manifest, errors }, null, 2));
}

async function postPromptResult(task, body, artifactResult) {
  if (!artifactResult.artifacts.length) return apiPost("/result", { ...body, artifact_errors: artifactResult.errors });
  try {
    return await apiPost("/result", { ...body, artifacts: artifactResult.artifacts, artifact_errors: artifactResult.errors });
  } catch (error) {
    if (![400, 413, 422].includes(error.status)) throw error;
    await spoolArtifacts(task.task_id, artifactResult.artifacts, artifactResult.errors);
    return apiPost("/result", { ...body, artifact_delivery: "spooled", artifact_errors: artifactResult.errors });
  }
}

async function handlePrompt(page, task) {
  const { task_id } = task;
  log(`prompt task ${task_id} (followup=${!!task.is_followup})`);
  await page.bringToFront().catch(() => {});
  let prepared = null;
  try {
    let actualMode;
    let actualModel = {};
    if (task.is_followup) {
      const detectedMode = await verifyFollowupConversation(page, task);
      actualMode = resolveTaskMode(task, detectedMode);
    } else {
      const marker = TAB_URL_MATCH ? `?${TAB_URL_MATCH}` : "";
      await page.goto(`https://chatgpt.com/${marker}`, { waitUntil: "domcontentloaded", timeout: 120000 });
      await markCompanyTab(page);
      await installDomCore(page);
      await page.bringToFront().catch(() => {});
      await sleep(1000);
      actualMode = resolveTaskMode(task);
      await ack(task_id, `selecting_${actualMode}`);
      await selectAndVerifyMode(page, actualMode);
      if (task.required_project_url) {
        await page.goto(task.required_project_url, { waitUntil: "domcontentloaded", timeout: 120000 });
        await installDomCore(page);
      }
      await ack(task_id, "selecting_model");
      actualModel = await configureModel(page, task);
    }

    await ack(task_id, "page_ready");
    prepared = await prepareTaskFiles(task);
    if (prepared) {
      await ack(task_id, "uploading_files");
      await uploadTaskFiles(page, task, prepared);
    }

    const input = page
      .locator("#prompt-textarea, div[contenteditable='true'][role='textbox'], textarea[data-testid='prompt-textarea']")
      .first();
    await input.waitFor({ state: "visible", timeout: 60000 });
    await input.click();
    await input.fill(task.prompt);
    await sleep(300);

    const beforeCount = await page.evaluate(() => window.__nyx.assistantCount());
    const sendBtn = page
      .locator("button[data-testid='send-button'], button[aria-label='Send prompt'], button[aria-label='Send message']")
      .first();
    await sendBtn.click({ timeout: 30000 });
    await ack(task_id, "sent");

    const response = await waitForResponse(page, task_id, beforeCount);
    for (let i = 0; i < 30 && !conversationId(page.url()); i++) await sleep(500);
    const chatgpt_url = page.url();
    if (!response || !response.trim()) {
      await apiPost("/result", { task_id, worker: LABEL, response: "ERROR: empty extraction", chatgpt_url, model: task.model });
      log(`prompt ${task_id} -> empty`);
      return;
    }

    const artifactResult = await collectArtifacts(page.context(), page);
    const res = await postPromptResult(task, {
      task_id,
      worker: LABEL,
      response,
      chatgpt_url,
      conversation_url: chatgpt_url,
      mode: actualMode,
      model: actualModel.model || task.model || "",
      model_settings: actualModel,
    }, artifactResult);
    log(`prompt ${task_id} -> ${res.status} (${response.length} chars, ${artifactResult.artifacts.length} artifacts)`);
  } finally {
    if (prepared?.dir) await rm(prepared.dir, { recursive: true, force: true }).catch(() => {});
  }
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
      const cancelled = await ack(task_id, "waiting_response");
      if (cancelled) throw new Error("cancelled by server");
    }
    const [generating, count, text] = await page.evaluate(() => [
      window.__nyx.isStillGenerating(),
      window.__nyx.assistantCount(),
      window.__nyx.extractResponse(),
    ]);
    if (count <= beforeCount) continue; // answer not yet appended
    if (generating) {
      stable = 0;
      continue;
    }
    const key = (text || "").slice(0, 200) + "|" + (text || "").length;
    if (key === lastKey && text && text.length > 0) {
      stable += 1;
      if (stable >= 2) return text;
    } else {
      stable = 0;
      lastKey = key;
    }
  }
  // Timed out. Only return text if a NEW assistant message actually appeared
  // since we sent the prompt; otherwise the latest message is stale (a
  // previous turn), so return "" and let the server mark the task failed
  // instead of handing back the wrong answer.
  const [count, text] = await page.evaluate(() => [
    window.__nyx.assistantCount(),
    window.__nyx.extractResponse(),
  ]);
  return count > beforeCount ? text : "";
}

// ── Scrape flow (attach existing conversation) ───────────────────────────
async function loadFullTranscript(page) {
  let renderedCount = 0;
  const renderStart = Date.now();
  while (Date.now() - renderStart < 20000) {
    renderedCount = await page.evaluate(() => document.querySelectorAll("[data-message-author-role]").length);
    if (renderedCount > 0) break;
    await sleep(700);
  }
  await sleep(1500);

  await expandCollapsibles(page);

  const result = await page.evaluate(async () => {
    const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
    const nyx = window.__nyx || {};
    const clean = (text) => nyx.cleanText ? nyx.cleanText(text || "") : (text || "").trim();
    const extract = (el) => nyx.extractTextWithMath ? nyx.extractTextWithMath(el) : ((el && el.innerText) || "");
    const wraps = Array.from(document.querySelectorAll('[data-testid^="conversation-turn"]')).slice(0, 2000);

    if (wraps.length > 0) {
      const turns = [];
      const seen = new Set();
      for (const w of wraps) {
        try {
          w.scrollIntoView({ block: "center" });
        } catch (e) {}
        await sleep(150);
        const key = w.getAttribute("data-testid");
        if (!key || seen.has(key)) continue;
        const roleEls = Array.from(w.querySelectorAll("[data-message-author-role]"));
        let role = "";
        let text = "";
        for (let i = roleEls.length - 1; i >= 0; i--) {
          const roleEl = roleEls[i];
          const candidateRole = roleEl.getAttribute("data-message-author-role");
          if (candidateRole !== "user" && candidateRole !== "assistant") continue;
          const candidateText = candidateRole === "assistant" && nyx.extractAssistantContent
            ? nyx.extractAssistantContent(roleEl)
            : clean(extract(roleEl));
          if (!candidateText) continue;
          role = candidateRole;
          text = candidateText.slice(0, 200000);
          break;
        }
        if (!text) continue;
        seen.add(key);
        turns.push({ role, text });
      }
      return { rendered: wraps.length, turns };
    }

    let lastHeight = -1;
    let stableHeight = 0;
    for (let i = 0; i < 50; i++) {
      try {
        const sc = nyx.scrollContainer();
        sc.scrollTop = 0;
      } catch (e) {}
      await sleep(700);
      let height = 0;
      try {
        const sc = nyx.scrollContainer();
        height = sc.scrollHeight || 0;
      } catch (e) {}
      if (height === lastHeight) {
        stableHeight += 1;
        if (stableHeight >= 3) break;
      } else {
        stableHeight = 0;
        lastHeight = height;
      }
    }

    const acc = new Map();
    const order = [];
    let rendered = document.querySelectorAll("[data-message-author-role]").length;
    let bottomStable = 0;
    for (let i = 0; i < 120 && acc.size < 2000; i++) {
      const snapshot = nyx.extractTranscriptKeys();
      rendered = Math.max(rendered, snapshot.rendered || 0);
      for (const turn of snapshot.turns || []) {
        const text = (turn.text || "").slice(0, 200000);
        if (!text) continue;
        if (!acc.has(turn.key)) order.push(turn.key);
        acc.set(turn.key, { role: turn.role, text });
        if (acc.size >= 2000) {
          break;
        }
      }

      try {
        const sc = nyx.scrollContainer();
        const step = Math.floor((sc.clientHeight || window.innerHeight || 800) * 0.8);
        sc.scrollTop = Math.min(sc.scrollHeight, sc.scrollTop + step);
      } catch (e) {}
      await sleep(600);
      let atBottom = false;
      try {
        const sc = nyx.scrollContainer();
        atBottom = sc.scrollTop + sc.clientHeight >= sc.scrollHeight - 4;
      } catch (e) {}
      if (atBottom) {
        bottomStable += 1;
        if (bottomStable >= 2) break;
      } else {
        bottomStable = 0;
      }
    }
    return { rendered, turns: order.map((key) => acc.get(key)).filter(Boolean) };
  });

  const turns = result.turns || [];
  renderedCount = Math.max(renderedCount, result.rendered || 0);
  log(`scrape: rendered≈${renderedCount} turns, accumulated ${turns.length}`);
  return turns;
}

async function handleScrape(page, task) {
  const { task_id, conversation_url } = task;
  log(`scrape task ${task_id} → ${conversation_url}`);
  await page.bringToFront().catch(() => {});
  if (!conversation_url) {
    await apiPost("/transcript", { task_id, worker: LABEL, turns: [], chatgpt_url: page.url() });
    return;
  }
  await page.goto(conversation_url, { waitUntil: "domcontentloaded" });
  await installDomCore(page);
  await page.bringToFront().catch(() => {});
  await ack(task_id, "scraping");

  const turns = await loadFullTranscript(page);
  const res = await apiPost("/transcript", { task_id, worker: LABEL, turns, chatgpt_url: page.url() });
  log(`scrape ${task_id} → ${res.status} (${turns.length} turns, ${res.imported_pairs} pairs)`);
}

// ── General web extraction flow ──────────────────────────────────────────
async function scrollLazyPage(page) {
  let lastHeight = -1;
  let stableHeight = 0;
  for (let i = 0; i < 6; i++) {
    const height = await page.evaluate(() => {
      const sc = document.scrollingElement || document.documentElement || document.body;
      const before = sc ? sc.scrollHeight : document.body.scrollHeight;
      try {
        if (sc) sc.scrollTop = before;
        else window.scrollTo(0, before);
      } catch (e) {
        try { window.scrollTo(0, before); } catch (inner) {}
      }
      return before || 0;
    });
    await sleep(600);
    const nextHeight = await page.evaluate(() => {
      const sc = document.scrollingElement || document.documentElement || document.body;
      return (sc && sc.scrollHeight) || document.body.scrollHeight || 0;
    });
    if (nextHeight === lastHeight || nextHeight === height) {
      stableHeight += 1;
      if (stableHeight >= 2) break;
    } else {
      stableHeight = 0;
    }
    lastHeight = nextHeight;
  }
}

async function expandCollapsibles(page) {
  try {
    await page.evaluate(() => {
      try {
        const root = document.querySelector("main") || document.body;
        if (!root) return;
        const isVisible = (el) => {
          const r = el.getBoundingClientRect();
          const style = getComputedStyle(el);
          return r.width > 0 && r.height > 0 && style.visibility !== "hidden" && style.display !== "none";
        };
        const inComposerOrChrome = (el) => {
          const text = (el.innerText || el.textContent || "").trim();
          if (el.closest("#prompt-textarea, form, textarea, [contenteditable='true'][role='textbox'], [class*='composer'], [data-testid='composer'], [data-testid='send-button'], [data-testid='stop-button']")) {
            return true;
          }
          if (el.matches("button.__composer-pill, button[aria-haspopup='menu'], button[data-testid='send-button'], button[data-testid='stop-button']")) {
            return true;
          }
          if (/^(Send|Stop|发送|停止|GPT-|Pro|极速|均衡|高级|超高)$/i.test(text)) return true;
          return false;
        };
        let clicked = 0;
        for (const detail of Array.from(root.querySelectorAll("details:not([open])"))) {
          if (clicked >= 40) break;
          try {
            detail.open = true;
            clicked += 1;
          } catch (e) {}
        }
        const candidates = Array.from(root.querySelectorAll('[aria-expanded="false"], button, [role="button"]'));
        for (const el of candidates) {
          if (clicked >= 40) break;
          try {
            if (!isVisible(el) || inComposerOrChrome(el)) continue;
            const text = (el.innerText || el.textContent || el.getAttribute("aria-label") || "").trim();
            const collapsed = el.getAttribute("aria-expanded") === "false";
            const looksExpandable = collapsed || /Thought for|思考|显示更多|Show more|展开/i.test(text);
            if (!looksExpandable) continue;
            el.click();
            clicked += 1;
          } catch (e) {}
        }
      } catch (e) {}
    });
    await sleep(300);
  } catch (e) {}
}

async function handleExtract(page, task) {
  const { task_id } = task;
  let targetHost = "-";
  try {
    targetHost = new URL(task.target_url).host || "-";
  } catch (e) {}
  log(`extract task ${task_id} → host=${targetHost}`);
  try {
    // Defense-in-depth SSRF check at navigation time (catches DNS rebinding
    // the server-side guard can't see); explicit timeout so a slow/hostile
    // URL can't stall this single worker page.
    await assertPublicTarget(task.target_url);
    await page.goto(task.target_url, {
      waitUntil: "domcontentloaded",
      timeout: 30000,
    });
    await page.bringToFront().catch(() => {});
    await page.waitForLoadState("networkidle", { timeout: 8000 }).catch(() => {});
    await ack(task_id, "extracting");
    await scrollLazyPage(page);
    await expandCollapsibles(page);
    const content = await page.evaluate(() => {
      const root = document.querySelector("main, article") || document.body;
      return ((root && root.innerText) || "").trim().slice(0, 200000);
    });
    const response = content || "ERROR: empty extraction";
    const res = await apiPost("/result", {
      task_id,
      worker: LABEL,
      response,
      chatgpt_url: page.url(),
      model: task.model,
    });
    log(`extract ${task_id} → ${res.status} (${content.length} chars)`);
  } catch (err) {
    await apiPost("/result", {
      task_id,
      worker: LABEL,
      response: `ERROR: ${err.message}`,
      chatgpt_url: page.url(),
      model: task.model,
    });
  }
}

async function ack(task_id, phase) {
  try {
    const r = await apiPost("/ack", { task_id, worker: LABEL, phase });
    return r.status === "cancelled";
  } catch (e) {
    return false;
  }
}

// ── Main loop ────────────────────────────────────────────────────────────
async function main() {
  log(`connecting to Chrome at ${CDP_URL} …`);
  const browser = await chromium.connectOverCDP(CDP_URL);
  const context = browser.contexts()[0] || (await browser.newContext());
  let page = await getChatPage(context);
  log(`attached. worker=${LABEL} pool=${BASE_URL}. polling…`);
  let networkFailures = 0;

  for (;;) {
    let delayMs = POLL_MS;
    try {
      if (page.isClosed()) page = await getChatPage(context);
      const resp = await apiGet(
        `/task?worker=${encodeURIComponent(LABEL)}&script_version=${SCRIPT_VERSION}&page_url=${encodeURIComponent(page.url())}`
      );
      networkFailures = 0;
      if (resp.status === "task" && resp.task_id) {
        try {
          if (resp.kind === "scrape") await handleScrape(page, resp);
          else if (resp.kind === "extract") await handleExtract(page, resp);
          else await handlePrompt(page, resp);
        } catch (err) {
          log(`task ${resp.task_id} errored: ${err.message}`);
          // Report the failure so the task doesn't hang until lease expiry.
          try {
            if (resp.kind === "scrape") {
              await apiPost("/transcript", { task_id: resp.task_id, worker: LABEL, turns: [], chatgpt_url: page.url() });
            } else {
              await apiPost("/result", { task_id: resp.task_id, worker: LABEL, response: `ERROR: ${err.message}`, chatgpt_url: page.url(), model: resp.model });
            }
          } catch (e) {}
        }
      }
    } catch (err) {
      if (err.status === 401 || err.status === 403) {
        // Distinct, loud signal: a revoked/invalid worker token (or an
        // inactive pool) otherwise loops quietly forever. Back off hard so
        // we don't hammer the server while still recovering if the token is
        // rotated back.
        log(
          `AUTH FAILED (HTTP ${err.status}): worker token rejected. Verify NYXID_WORKER_TOKEN and that the pool is active. Backing off…`
        );
        delayMs = Math.max(POLL_MS, 30000);
      } else {
        networkFailures += 1;
        delayMs = boundedBackoffMs(networkFailures - 1, POLL_MS, 120000);
        log(`poll error: ${err.message}; retrying in ${delayMs}ms`);
      }
    }
    await sleep(delayMs);
  }
}

main().catch((e) => {
  console.error("fatal:", e);
  process.exit(1);
});
