import path from "node:path";

const CHAT_REVIEW_KINDS = new Set([
  "fresh_review",
  "targeted_review",
  "targeted_verification",
  "literature_research",
  "deep_research",
]);

const MIME_EXTENSIONS = new Map([
  ["image/png", ".png"],
  ["image/jpeg", ".jpg"],
  ["image/webp", ".webp"],
  ["image/gif", ".gif"],
  ["image/svg+xml", ".svg"],
  ["application/pdf", ".pdf"],
]);

function titleCase(value) {
  const trimmed = String(value || "").trim();
  return trimmed ? trimmed[0].toUpperCase() + trimmed.slice(1).toLowerCase() : "";
}

export function resolveTaskMode(task = {}, detectedFollowupMode = "") {
  if (task.is_followup) {
    const detected = String(detectedFollowupMode || "").trim().toLowerCase();
    if (detected === "chat" || detected === "work") return detected;
    throw new Error("follow-up conversation mode could not be detected");
  }

  const explicit = String(task.mode || "auto").trim().toLowerCase();
  if (explicit === "chat" || explicit === "work") return explicit;
  const reviewKind = String(task.review_kind || task.context_mode || "").trim().toLowerCase();
  return CHAT_REVIEW_KINDS.has(reviewKind) ? "chat" : "work";
}

export function boundedBackoffMs(failures, baseMs = 5000, maxMs = 120000) {
  const exponent = Math.max(0, Math.min(30, Number(failures) || 0));
  return Math.min(maxMs, baseMs * (2 ** exponent));
}

export function normalizeModelRequest(task = {}) {
  const rawModel = String(task.model || "").trim();
  const power = Number.isFinite(Number(task.power))
    ? Math.max(1, Math.min(5, Math.round(Number(task.power))))
    : null;
  return {
    model: rawModel.toLowerCase() === "unknown" ? "" : rawModel,
    effort: titleCase(task.effort),
    speed: titleCase(task.speed),
    power,
  };
}

export function safeArtifactName(name, index = 1, mimeType = "") {
  const original = path.basename(String(name || "").replaceAll("\\", "/"));
  let safe = original
    .replace(/[<>:"/\\|?*\u0000-\u001f]/g, "_")
    .replace(/^\.+/, "")
    .trim();
  if (!safe) safe = `artifact-${index}`;
  if (!path.extname(safe)) safe += MIME_EXTENSIONS.get(String(mimeType).toLowerCase()) || ".bin";
  return safe;
}

export function conversationId(rawUrl) {
  try {
    const url = new URL(String(rawUrl || ""));
    if (!/^(chatgpt\.com|chat\.openai\.com)$/i.test(url.hostname)) return "";
    return url.pathname.match(/^\/c\/([a-z0-9-]{6,})/i)?.[1] || "";
  } catch {
    return "";
  }
}
