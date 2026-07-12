# NyxID ChatGPT Shared Worker Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the stopped local Oracle path with three fixed company workers that support Chat/Work, current ChatGPT 5.6 model controls, file upload, artifact return, and reliable follow-up while keeping WARP under explicit user control.

**Architecture:** Put all maintained worker and launcher code under `tools/chatgpt-oracle/nyxid-worker/`. Keep `.nyxid-oracle/` as local state only and redirect its entry points to the tracked launchers. Separate pure task/DOM policy helpers from the CDP loop so Node tests can validate routing, follow-up invariants, selectors, artifact metadata, and retry behavior without a live browser.

**Tech Stack:** Node.js 22 ESM, Playwright Core over Chrome CDP, Undici proxy dispatcher, PowerShell 5.1 launchers, Node built-in test runner, Python static integration tests.

---

### Task 1: Establish the tracked NyxID worker source and pure policy module

**Files:**
- Create: `tools/chatgpt-oracle/nyxid-worker/policy.mjs`
- Create: `tools/chatgpt-oracle/nyxid-worker/policy.test.mjs`
- Create: `tools/chatgpt-oracle/nyxid-worker/package.json`
- Create: `tools/chatgpt-oracle/nyxid-worker/README.md`

- [ ] **Step 1: Write failing policy tests**

Test `resolveTaskMode()` mappings for contextual execution, architecture audit, fresh review, targeted review, explicit overrides, and follow-up mode preservation. Test `boundedBackoffMs()` and artifact filename/MIME normalization.

```javascript
import test from "node:test";
import assert from "node:assert/strict";
import { resolveTaskMode, boundedBackoffMs } from "./policy.mjs";

test("routes contextual audits to Work and fresh reviews to Chat", () => {
  assert.equal(resolveTaskMode({ mode: "auto", review_kind: "contextual_execution" }), "work");
  assert.equal(resolveTaskMode({ mode: "auto", review_kind: "fresh_review" }), "chat");
});

test("follow-up preserves the detected conversation mode", () => {
  assert.equal(resolveTaskMode({ mode: "chat", is_followup: true }, "work"), "work");
});

test("network retry is bounded", () => {
  assert.equal(boundedBackoffMs(0, 5000, 120000), 5000);
  assert.equal(boundedBackoffMs(99, 5000, 120000), 120000);
});
```

- [ ] **Step 2: Run the policy test and verify RED**

Run: `node --test tools/chatgpt-oracle/nyxid-worker/policy.test.mjs`

Expected: FAIL because `policy.mjs` and its exports do not exist.

- [ ] **Step 3: Implement minimal pure helpers**

Implement and export:

```javascript
export function resolveTaskMode(task, detectedFollowupMode = "") { /* explicit, follow-up, auto mapping */ }
export function boundedBackoffMs(failures, baseMs = 5000, maxMs = 120000) { /* capped exponential */ }
export function normalizeModelRequest(task) { /* model, effort, speed, power */ }
export function safeArtifactName(name, index, mimeType) { /* path-safe deterministic name */ }
export function conversationId(url) { /* /c/<id> extraction */ }
```

- [ ] **Step 4: Run the policy test and verify GREEN**

Run: `node --test tools/chatgpt-oracle/nyxid-worker/policy.test.mjs`

Expected: all policy tests PASS.

### Task 2: Port and update the company CDP worker

**Files:**
- Create: `tools/chatgpt-oracle/nyxid-worker/worker.mjs`
- Create: `tools/chatgpt-oracle/nyxid-worker/worker-static.test.mjs`
- Modify: `tools/chatgpt-oracle/nyxid-worker/package.json`

- [ ] **Step 1: Write failing static behavior tests**

Assert that the new worker:

```javascript
assert.match(source, /getByRole\("radio", \{ name: modeLabel/);
assert.match(source, /data-state/);
assert.match(source, /\[data-testid\^=['"]conversation-turn/);
assert.doesNotMatch(source, /article\[data-testid\^=['"]conversation-turn/);
assert.match(source, /setInputFiles/);
assert.match(source, /collectArtifacts/);
assert.match(source, /verifyFollowupConversation/);
assert.match(source, /resolveTaskMode/);
```

- [ ] **Step 2: Run tests and verify RED**

Run: `node --test tools/chatgpt-oracle/nyxid-worker/*.test.mjs`

Expected: static test FAIL because `worker.mjs` is absent.

- [ ] **Step 3: Port the existing NyxID protocol and current answer extractor**

Move the behavior from `.nyxid-oracle/company-slot2-worker/worker-slot2.mjs` into the tracked worker. Preserve bearer authentication, SSRF checks, prompt/scrape/extract task kinds, reasoning exclusion, mathematical text extraction, task acknowledgement, and result reporting.

- [ ] **Step 4: Implement Chat/Work and model controls**

Add `selectAndVerifyMode(page, mode)` using exact `role=radio` labels and `data-state="on"`. Add hierarchical current-menu selection for Model, Effort, Speed, and the Power slider. Return the observed configuration in result metadata. Fresh tasks may select mode; follow-ups must not.

- [ ] **Step 5: Implement file upload**

Decode task `files`, legacy `pdf_base64`, and legacy `pdf_name` into a task-specific temporary directory. Use the visible/accept-compatible `input[type=file]`, lazy-mount it through `composer-plus-btn` and `Upload from computer` when necessary, call `setInputFiles`, and block send until upload progress clears and the send button is enabled. Always remove the temporary directory.

- [ ] **Step 6: Implement follow-up invariants**

For `is_followup`, require a valid `conversation_url`, navigate to it, compare requested and actual conversation IDs, detect existing Work markers, preserve mode, record assistant count, and only return a newly appended assistant turn. Never create a fresh conversation when follow-up verification fails.

- [ ] **Step 7: Implement artifact collection and compatible result reporting**

Collect final-answer images and Work Outputs links/images. Download HTTP resources with the authenticated browser context and blob resources in-page. Enforce 20 MiB per artifact, 50 MiB total, and 30-second per-download limits. Submit `artifacts` with `/result`; if the server rejects the field, retry the textual result and write artifacts to `.nyxid-oracle/artifact-spool/<task-id>/manifest.json`, reporting `artifact_delivery="spooled"`.

- [ ] **Step 8: Verify syntax and tests GREEN**

Run:

```powershell
node --check tools/chatgpt-oracle/nyxid-worker/worker.mjs
node --test tools/chatgpt-oracle/nyxid-worker/*.test.mjs
```

Expected: syntax exit 0 and all Node tests PASS.

### Task 3: Separate WARP lifecycle from workers

**Files:**
- Create: `tools/chatgpt-oracle/nyxid-worker/warp-control.ps1`
- Create: `tools/chatgpt-oracle/nyxid-worker/start-worker.ps1`
- Create: `tools/chatgpt-oracle/nyxid-worker/start-shared.ps1`
- Create: `tools/chatgpt-oracle/nyxid-worker/launcher-static.test.ps1`

- [ ] **Step 1: Write failing launcher assertions**

Assert that default labels are exactly `company_win_work_1..3`, only `start-shared.ps1` calls `warp-cli connect`, `start-worker.ps1` contains no `warp-cli` invocation, and worker environment points to the tracked `worker.mjs` and company token file.

- [ ] **Step 2: Run static launcher tests and verify RED**

Run: `powershell -ExecutionPolicy Bypass -File tools/chatgpt-oracle/nyxid-worker/launcher-static.test.ps1`

Expected: FAIL because launchers do not exist.

- [ ] **Step 3: Implement explicit WARP start**

`warp-control.ps1 -Action Start` configures proxy port 40000, proxy mode, and connects once. It starts a localhost relay only if the relay is not already listening. `-Action Status` is read-only. No watchdog or restart loop is created.

- [ ] **Step 4: Implement one worker launcher**

`start-worker.ps1` validates Chrome CDP, worker source, company token, and proxy availability; sets label/tab marker/CDP/proxy environment; starts Node hidden; and writes PID/log files to `.nyxid-oracle`. Proxy unavailability fails the start clearly without connecting WARP.

- [ ] **Step 5: Implement shared stack launcher**

`start-shared.ps1` explicitly starts WARP once, opens/reuses the dedicated Chrome CDP profile, creates/reuses exactly three URL-marked ChatGPT tabs, and starts/reuses exactly three company workers. It verifies PIDs refer to the expected Node command rather than accepting arbitrary Node processes.

- [ ] **Step 6: Run launcher tests and verify GREEN**

Run: `powershell -ExecutionPolicy Bypass -File tools/chatgpt-oracle/nyxid-worker/launcher-static.test.ps1`

Expected: all assertions PASS.

### Task 4: Redirect local entry points and update repository integration tests

**Files:**
- Modify: `.nyxid-oracle/start-all.ps1`
- Modify: `.nyxid-oracle/start-cdp-worker.ps1`
- Modify: `.nyxid-oracle/NyxID Oracle Worker.cmd`
- Modify: `tools/chatgpt-oracle/tests/test_nyxid_oracle_scripts_static.py`

- [ ] **Step 1: Extend Python tests for the new truth source**

Replace assertions for `company-slot2-worker/worker-slot2.mjs` with the tracked worker path. Assert the thin local entry point delegates to `tools/chatgpt-oracle/nyxid-worker/start-shared.ps1`, defaults to company labels only, and contains no local token default.

- [ ] **Step 2: Run Python tests and verify RED**

Run: `python -m pytest tools/chatgpt-oracle/tests/test_nyxid_oracle_scripts_static.py -q`

Expected: FAIL against the old local launchers.

- [ ] **Step 3: Replace local scripts with thin delegates**

Preserve `.nyxid-oracle` token/PID/log files. Delegate shared startup and individual worker startup to the tracked PowerShell scripts with `-StateDir $PSScriptRoot`. The CMD entry point invokes the tracked shared launcher.

- [ ] **Step 4: Run integration tests and verify GREEN**

Run:

```powershell
python -m pytest tools/chatgpt-oracle/tests/test_nyxid_oracle_scripts_static.py -q
python -m pytest tools/chatgpt-oracle/tests/test_cdp_worker_static.py -q
```

Expected: all tests PASS.

### Task 5: Install dependencies and perform complete automated verification

**Files:**
- Create: `tools/chatgpt-oracle/nyxid-worker/package-lock.json`

- [ ] **Step 1: Install locked dependencies**

Run: `npm install --prefix tools/chatgpt-oracle/nyxid-worker`

Expected: package lock created with Playwright Core and Undici; exit 0.

- [ ] **Step 2: Run focused verification**

Run:

```powershell
npm test --prefix tools/chatgpt-oracle/nyxid-worker
python -m pytest tools/chatgpt-oracle/tests/test_nyxid_oracle_scripts_static.py tools/chatgpt-oracle/tests/test_cdp_worker_static.py -q
```

Expected: all Node and Python tests PASS.

- [ ] **Step 3: Run diff and syntax checks**

Run:

```powershell
git -c safe.directory=D:/omega/automath diff --check
node --check tools/chatgpt-oracle/nyxid-worker/worker.mjs
```

Expected: no whitespace errors and syntax exit 0.

### Task 6: Activate and live-verify the shared stack

**Files:**
- Runtime state only: `.nyxid-oracle/*.pid`, `.nyxid-oracle/*.log`, `.nyxid-oracle/artifact-spool/`

- [ ] **Step 1: Start WARP and the shared stack explicitly**

Run: `powershell -ExecutionPolicy Bypass -File tools/chatgpt-oracle/nyxid-worker/start-shared.ps1`

Expected: WARP connected, relay reachable, Chrome CDP available, and three fixed worker PIDs started.

- [ ] **Step 2: Verify three fixed tabs over CDP**

Inspect `http://127.0.0.1:9222/json/list` and verify exactly one page marker for each `company_win_work_1`, `company_win_work_2`, and `company_win_work_3`.

- [ ] **Step 3: Verify worker registration and logs**

Check each worker log for `attached` and successful polling. Confirm no `tab_1..3` local worker was started and no authentication token appears in logs.

- [ ] **Step 4: Run non-destructive live DOM probes**

On a fixed tab, verify Chat/Work radios, current model menu, composer, file input, send button, and tag-independent conversation turn selectors. Do not send a prompt unless a safe NyxID smoke task is available.

- [ ] **Step 5: Verify manual WARP shutdown semantics structurally and operationally**

Confirm no worker or monitor command line contains `warp-cli`. After a deliberate `warp-cli disconnect`, observe worker network backoff without WARP reconnection, then explicitly run the shared launcher to restore service. This is the only operational step allowed to reconnect WARP.

- [ ] **Step 6: Report exact live-test limits**

If no server-side smoke task is available, report PDF, artifact, and follow-up behavior as automated/DOM verified but not claim a completed remote round trip. If a smoke task is available, verify first prompt, artifact return, and one follow-up against the same conversation ID.
