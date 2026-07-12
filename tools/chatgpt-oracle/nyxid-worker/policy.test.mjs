import test from "node:test";
import assert from "node:assert/strict";

import {
  boundedBackoffMs,
  conversationId,
  normalizeModelRequest,
  resolveTaskMode,
  safeArtifactName,
} from "./policy.mjs";

test("routes contextual audits to Work and fresh reviews to Chat", () => {
  assert.equal(resolveTaskMode({ mode: "auto", review_kind: "contextual_execution" }), "work");
  assert.equal(resolveTaskMode({ mode: "auto", review_kind: "architecture_audit" }), "work");
  assert.equal(resolveTaskMode({ mode: "auto", review_kind: "fresh_review" }), "chat");
  assert.equal(resolveTaskMode({ mode: "auto", review_kind: "targeted_verification" }), "chat");
});

test("respects explicit fresh-task mode", () => {
  assert.equal(resolveTaskMode({ mode: "chat" }), "chat");
  assert.equal(resolveTaskMode({ mode: "work" }), "work");
});

test("follow-up preserves the detected conversation mode", () => {
  assert.equal(resolveTaskMode({ mode: "chat", is_followup: true }, "work"), "work");
  assert.equal(resolveTaskMode({ mode: "work", is_followup: true }, "chat"), "chat");
  assert.throws(() => resolveTaskMode({ is_followup: true }), /mode/i);
});

test("network retry is exponential and bounded", () => {
  assert.equal(boundedBackoffMs(0, 5000, 120000), 5000);
  assert.equal(boundedBackoffMs(1, 5000, 120000), 10000);
  assert.equal(boundedBackoffMs(99, 5000, 120000), 120000);
});

test("normalizes current ChatGPT model controls", () => {
  assert.deepEqual(normalizeModelRequest({
    model: " GPT-5.6 Sol ",
    effort: " ultra ",
    speed: "standard",
    power: 9,
  }), {
    model: "GPT-5.6 Sol",
    effort: "Ultra",
    speed: "Standard",
    power: 5,
  });
});

test("treats legacy unknown model as no model override", () => {
  assert.equal(normalizeModelRequest({ model: "unknown" }).model, "");
});

test("extracts conversation IDs and rejects unrelated URLs", () => {
  assert.equal(conversationId("https://chatgpt.com/c/6a523232-03e8-83ec-a3a9-8f6cca466818"), "6a523232-03e8-83ec-a3a9-8f6cca466818");
  assert.equal(conversationId("https://example.com/c/not-chatgpt"), "");
});

test("creates path-safe artifact names with MIME extensions", () => {
  assert.equal(safeArtifactName("..\\chart", 2, "image/png"), "chart.png");
  assert.equal(safeArtifactName("", 3, "application/pdf"), "artifact-3.pdf");
});
