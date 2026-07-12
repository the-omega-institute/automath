import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

const source = readFileSync(new URL("./worker.mjs", import.meta.url), "utf8");

test("uses current tag-independent ChatGPT turn selectors", () => {
  assert.match(source, /\[data-testid\^=["']conversation-turn/);
  assert.doesNotMatch(source, /article\[data-testid\^=["']conversation-turn/);
  assert.match(source, /data-message-author-role/);
});

test("selects and verifies Chat or Work by radio state", () => {
  assert.match(source, /getByRole\("radio", \{ name: modeLabel/);
  assert.match(source, /getAttribute\("data-state"\)/);
  assert.match(source, /selectAndVerifyMode/);
});

test("claims a pre-created tab by URL marker before storage is initialized", () => {
  assert.match(source, /url\.includes\(TAB_URL_MATCH\) \|\| await pageHasStorageMarker\(page\)/);
});

test("supports current hierarchical model controls", () => {
  assert.match(source, /configureModel/);
  assert.match(source, /Model/);
  assert.match(source, /Effort/);
  assert.match(source, /Speed/);
  assert.match(source, /role=.slider./);
});

test("uploads files and collects output artifacts", () => {
  assert.match(source, /setInputFiles/);
  assert.match(source, /Upload from computer/);
  assert.match(source, /collectArtifacts/);
  assert.match(source, /artifact-spool/);
});

test("enforces follow-up conversation identity and mode", () => {
  assert.match(source, /verifyFollowupConversation/);
  assert.match(source, /conversationId/);
  assert.match(source, /resolveTaskMode/);
  assert.match(source, /follow-up/);
});

test("backs off network failures without controlling WARP", () => {
  assert.match(source, /boundedBackoffMs/);
  assert.doesNotMatch(source, /warp-cli|Cloudflare WARP/i);
});

test("defaults to a company identity rather than the retired local pool", () => {
  assert.match(source, /NYXID_WORKER_LABEL \|\| "company_win_work_1"/);
  assert.doesNotMatch(source, /NYXID_WORKER_LABEL \|\| "tab_1"/);
});
