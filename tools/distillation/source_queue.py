#!/usr/bin/env python3
"""Source queue for expanding Omega distillation beyond completed sources."""

from __future__ import annotations

import hashlib
import json
from datetime import datetime
from typing import Any

try:
    from tools.distillation import distill
except ModuleNotFoundError:  # pragma: no cover - supports direct script imports
    import distill


SOURCE_QUEUE_PATH = distill.BACKFLOW_DIR / "source_queue.json"
QUEUE_VERSION = 1
DEFAULT_SEED_LIMIT = 24
DEFAULT_ORACLE_LIMIT = 12
TERMINAL_SEED_STATUSES = {"covered_by_oracle", "accepted", "running", "done", "rejected"}


def _now_iso() -> str:
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def _json(data: Any) -> str:
    return json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True)


def _stable_for_compare(data: dict[str, Any]) -> dict[str, Any]:
    stable = json.loads(_json(data))
    if isinstance(stable, dict):
        stable.pop("updated_at", None)
        stable.pop("oracle_source_queue", None)
    return stable


def _digest(*parts: str) -> str:
    text = "|".join(str(part) for part in parts)
    return hashlib.sha1(text.encode("utf-8")).hexdigest()[:12]


def _candidate_id(prefix: str, proposed_source: str, target_sections: list[str], origin: str) -> str:
    return f"{prefix}:{_digest(proposed_source, ','.join(target_sections), origin)}"


def read_queue() -> dict[str, Any]:
    if not SOURCE_QUEUE_PATH.exists():
        return {
            "version": QUEUE_VERSION,
            "description": (
                "Candidate queue for future Omega distillation sources. "
                "Oracle may enrich discovery seeds, but Codex+Claude still gate writeback."
            ),
            "updated_at": "",
            "candidates": [],
        }
    data = distill.read_json(SOURCE_QUEUE_PATH)
    if not isinstance(data, dict):
        return {"version": QUEUE_VERSION, "updated_at": "", "candidates": []}
    candidates = data.get("candidates", [])
    if not isinstance(candidates, list):
        candidates = []
    data["version"] = int(data.get("version", QUEUE_VERSION) or QUEUE_VERSION)
    data["candidates"] = [item for item in candidates if isinstance(item, dict)]
    return data


def write_queue(queue: dict[str, Any]) -> None:
    queue["version"] = QUEUE_VERSION
    queue["updated_at"] = _now_iso()
    distill.write_json(SOURCE_QUEUE_PATH, queue)


def _existing_source_slugs() -> set[str]:
    return {distill._slugify(name) for name in distill._existing_state_names()}


def _memory_entries() -> list[dict[str, Any]]:
    memory = distill._read_distillation_memory()
    return [entry for entry in memory.get("entries", []) if isinstance(entry, dict)]


def _priority_for_entry(entry: dict[str, Any]) -> int:
    kind = str(entry.get("kind", ""))
    sections = distill._unique_strings(entry.get("target_sections", []))
    base = 40 if kind == "oracle_sidecar" else 30
    return min(80, base + 4 * len(sections))


def discovery_seeds_from_memory(
    entries: list[dict[str, Any]] | None = None,
    *,
    limit: int = DEFAULT_SEED_LIMIT,
) -> list[dict[str, Any]]:
    """Convert memory entries into Oracle-ready source discovery seeds."""
    rows = entries if entries is not None else _memory_entries()
    seeds: list[dict[str, Any]] = []
    seen: set[str] = set()
    for entry in rows:
        if str(entry.get("status", "open")) not in {"open", "active"}:
            continue
        sections = distill._unique_strings(entry.get("target_sections", []))
        if not sections:
            continue
        source = str(entry.get("source", "")).strip() or "unknown source"
        origin_id = str(entry.get("id", "")).strip()
        semantic_key = f"{distill._slugify(source)}|{','.join(sections)}"
        if semantic_key in seen:
            continue
        proposed = f"Oracle source discovery for {', '.join(sections)} after {source}"
        candidate_id = _candidate_id("seed", proposed, sections, origin_id)
        seen.add(semantic_key)
        seeds.append(
            {
                "id": candidate_id,
                "status": "needs_oracle",
                "priority": _priority_for_entry(entry),
                "proposed_source": proposed,
                "source_type": "discovery_seed",
                "seed_source": source,
                "origin": "distillation_memory",
                "origin_entry_ids": [origin_id] if origin_id else [],
                "target_sections": sections,
                "omega_mechanisms": sections,
                "rationale": str(entry.get("reason", "")).strip(),
                "risks": [
                    "This is a mechanism gap, not yet a concrete mathematician or paper.",
                    "Use Oracle enrichment or human curation before running distillation.",
                ],
                "next_step": "oracle_source_discovery",
            }
        )
        if len(seeds) >= limit:
            break
    return seeds


def _build_oracle_prompt(
    seeds: list[dict[str, Any]],
    existing_sources: list[str],
    existing_queue: dict[str, Any],
    *,
    limit: int,
) -> str:
    current_candidates = [
        {
            "id": item.get("id"),
            "status": item.get("status"),
            "proposed_source": item.get("proposed_source"),
            "target_sections": item.get("target_sections", []),
        }
        for item in existing_queue.get("candidates", [])
        if isinstance(item, dict)
    ][:40]
    schema = {
        "candidates": [
            {
                "proposed_source": "mathematician, school, paper, or source cluster",
                "source_type": "mathematician|paper|school|topic_cluster",
                "priority": 1,
                "fit_score": 0,
                "novelty_score": 0,
                "target_sections": ["Omega section/mechanism"],
                "omega_mechanisms": ["mechanism this source may enrich"],
                "why_now": "why this is a good next distillation target",
                "source_material": ["canonical papers/books/results to inspect"],
                "risks": ["overlap, weak fit, or outreach risk"],
                "first_distillation_prompt": "one concrete prompt to start Stage R",
                "outreach_angle": "why this source is useful for outreach/new papers",
                "seed_ids": ["seed ids this candidate answers"],
            }
        ]
    }
    return (
        "You are the Oracle source-discovery layer for the Omega distillation pipeline.\n"
        "Goal: propose concrete future distillation sources that can produce new Omega "
        "theorem/proof writebacks and later outreach/new-paper directions.\n\n"
        "Existing completed sources; do not duplicate these as plain reruns:\n"
        f"{_json(existing_sources)}\n\n"
        "Current source queue snapshot; avoid duplicates:\n"
        f"{_json(current_candidates)}\n\n"
        "Discovery seeds from distillation memory. Each seed is a mechanism gap or "
        "sidecar result, not yet a concrete source:\n"
        f"{_json(seeds)}\n\n"
        f"Return at most {limit} high-quality candidates. Prefer named mathematicians, "
        "specific papers, or coherent schools whose known methods plausibly map to the "
        "target Omega mechanisms. Be selective; do not fill quota.\n\n"
        "Rules:\n"
        "- Do not propose the completed source itself unless the candidate is a clearly "
        "different paper/source cluster.\n"
        "- A candidate must have fit_score >= 7 and novelty_score >= 6.\n"
        "- Include source_material concrete enough for Codex to start Stage R.\n"
        "- Output JSON only with this schema:\n"
        f"{_json(schema)}"
    )


def _normalize_oracle_candidate(raw: dict[str, Any]) -> dict[str, Any] | None:
    proposed = str(raw.get("proposed_source", "")).strip()
    if not proposed:
        return None
    target_sections = distill._unique_strings(raw.get("target_sections", []))
    seed_ids = distill._unique_strings(raw.get("seed_ids", []))
    fit = int(raw.get("fit_score", 0) or 0)
    novelty = int(raw.get("novelty_score", 0) or 0)
    if fit < 7 or novelty < 6:
        return None
    candidate_id = _candidate_id("oracle", proposed, target_sections, ",".join(seed_ids))
    raw_priority = int(raw.get("priority", 50) or 50)
    priority = 100 - raw_priority if 1 <= raw_priority <= 12 else raw_priority
    priority = max(1, min(100, priority))
    return {
        "id": candidate_id,
        "status": "open",
        "priority": priority,
        "oracle_rank": raw_priority if 1 <= raw_priority <= 100 else None,
        "proposed_source": proposed,
        "source_type": str(raw.get("source_type", "topic_cluster") or "topic_cluster"),
        "origin": "oracle_source_queue",
        "origin_entry_ids": seed_ids,
        "target_sections": target_sections,
        "omega_mechanisms": distill._unique_strings(raw.get("omega_mechanisms", [])),
        "fit_score": fit,
        "novelty_score": novelty,
        "rationale": str(raw.get("why_now", "")).strip(),
        "source_material": distill._unique_strings(raw.get("source_material", [])),
        "risks": distill._unique_strings(raw.get("risks", [])),
        "first_distillation_prompt": str(raw.get("first_distillation_prompt", "")).strip(),
        "outreach_angle": str(raw.get("outreach_angle", "")).strip(),
        "next_step": "distill_source",
    }


def oracle_enrich_queue(
    seeds: list[dict[str, Any]],
    existing_queue: dict[str, Any],
    *,
    limit: int = DEFAULT_ORACLE_LIMIT,
    timeout_seconds: int = distill.DEFAULT_ORACLE_TIMEOUT,
    model: str = distill.DEFAULT_ORACLE_MODEL,
    dry_run: bool = False,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Ask the Oracle to turn discovery seeds into concrete source candidates."""
    if not seeds:
        return [], {"status": "skipped", "reason": "no discovery seeds"}
    prompt = _build_oracle_prompt(
        seeds,
        distill._existing_state_names(),
        existing_queue,
        limit=limit,
    )
    state = distill.DistillState(name="Source-Queue")
    response = distill.chatgpt_oracle_exec(
        state,
        prompt,
        log_tag="source_queue",
        timeout_seconds=timeout_seconds,
        model=model,
        dry_run=dry_run,
    )
    if not response:
        return [], {"status": "empty_response"}
    try:
        parsed = distill._extract_json(response)
    except ValueError as exc:
        return [], {"status": "parse_failed", "reason": str(exc)}
    raw_candidates = parsed.get("candidates", []) if isinstance(parsed, dict) else parsed
    if not isinstance(raw_candidates, list):
        return [], {"status": "schema_failed", "reason": "candidates is not a list"}
    candidates = []
    for raw in raw_candidates:
        if not isinstance(raw, dict):
            continue
        normalized = _normalize_oracle_candidate(raw)
        if normalized:
            candidates.append(normalized)
    return candidates[:limit], {"status": "ok", "accepted": len(candidates[:limit])}


def _merge_candidates(existing: list[dict[str, Any]], incoming: list[dict[str, Any]]) -> list[dict[str, Any]]:
    now = _now_iso()
    merged: dict[str, dict[str, Any]] = {}
    for item in existing:
        item_id = str(item.get("id", "")).strip()
        if item_id:
            merged[item_id] = dict(item)
    for item in incoming:
        item_id = str(item.get("id", "")).strip()
        if not item_id:
            continue
        previous = merged.get(item_id, {})
        combined = {**previous, **item}
        if (
            previous.get("source_type") == "discovery_seed"
            and item.get("status") == "needs_oracle"
            and previous.get("status") in TERMINAL_SEED_STATUSES
        ):
            combined["status"] = previous.get("status")
            combined["next_step"] = previous.get("next_step")
            combined["covered_by_candidates"] = previous.get("covered_by_candidates", [])
        combined.setdefault("created_at", previous.get("created_at") or now)
        previous_compare = {k: v for k, v in previous.items() if k != "updated_at"}
        combined_compare = {k: v for k, v in combined.items() if k != "updated_at"}
        if previous and previous_compare == combined_compare:
            combined["updated_at"] = previous.get("updated_at", now)
        else:
            combined["updated_at"] = now
        merged[item_id] = combined
    collapsed: dict[tuple[Any, ...], dict[str, Any]] = {}
    for item in merged.values():
        key = _semantic_candidate_key(item)
        previous = collapsed.get(key)
        if not previous:
            collapsed[key] = item
            continue
        combined = {**previous, **item}
        combined["id"] = previous.get("id") or item.get("id")
        combined["priority"] = max(
            int(previous.get("priority", 0) or 0),
            int(item.get("priority", 0) or 0),
        )
        combined["origin_entry_ids"] = distill._unique_strings(
            list(previous.get("origin_entry_ids", []) or [])
            + list(item.get("origin_entry_ids", []) or [])
        )
        combined["created_at"] = previous.get("created_at") or item.get("created_at") or now
        combined["updated_at"] = now
        collapsed[key] = combined
    return sorted(
        collapsed.values(),
        key=lambda item: (
            str(item.get("status", "")) != "open",
            -int(item.get("priority", 0) or 0),
            str(item.get("proposed_source", "")),
        ),
    )


def mark_covered_seeds(
    seeds: list[dict[str, Any]],
    oracle_candidates: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Mark discovery seeds answered by accepted Oracle candidates."""
    covered: dict[str, list[str]] = {}
    for candidate in oracle_candidates:
        candidate_id = str(candidate.get("id", "")).strip()
        if not candidate_id:
            continue
        for seed_id in distill._unique_strings(candidate.get("origin_entry_ids", [])):
            covered.setdefault(seed_id, []).append(candidate_id)
    if not covered:
        return seeds
    marked = []
    for seed in seeds:
        seed_id = str(seed.get("id", "")).strip()
        if seed_id not in covered:
            marked.append(seed)
            continue
        updated = dict(seed)
        updated["status"] = "covered_by_oracle"
        updated["next_step"] = "distill_source_candidate_opened"
        updated["covered_by_candidates"] = sorted(set(covered[seed_id]))
        marked.append(updated)
    return marked


def _semantic_candidate_key(item: dict[str, Any]) -> tuple[Any, ...]:
    status = str(item.get("status", ""))
    source_type = str(item.get("source_type", ""))
    sections = tuple(distill._unique_strings(item.get("target_sections", [])))
    if status == "needs_oracle" and source_type == "discovery_seed":
        return ("seed", distill._slugify(str(item.get("seed_source", ""))), sections)
    if str(item.get("origin", "")) == "oracle_source_queue":
        return ("oracle", distill._slugify(str(item.get("proposed_source", ""))), sections)
    return ("id", str(item.get("id", "")))


def refresh_source_queue(
    *,
    use_oracle: bool = False,
    seed_limit: int = DEFAULT_SEED_LIMIT,
    oracle_limit: int = DEFAULT_ORACLE_LIMIT,
    oracle_timeout: int = distill.DEFAULT_ORACLE_TIMEOUT,
    oracle_model: str = distill.DEFAULT_ORACLE_MODEL,
    dry_run: bool = False,
) -> dict[str, Any]:
    """Refresh source_queue.json from memory seeds and optional Oracle enrichment."""
    old_queue = read_queue()
    before = _json(_stable_for_compare(old_queue))
    seeds = discovery_seeds_from_memory(limit=seed_limit)
    oracle_status = {"status": "disabled"}
    oracle_candidates: list[dict[str, Any]] = []
    if use_oracle:
        oracle_candidates, oracle_status = oracle_enrich_queue(
            seeds,
            old_queue,
            limit=oracle_limit,
            timeout_seconds=oracle_timeout,
            model=oracle_model,
            dry_run=dry_run,
        )
        seeds = mark_covered_seeds(seeds, oracle_candidates)
    queue = {
        "version": QUEUE_VERSION,
        "description": old_queue.get(
            "description",
            "Candidate queue for future Omega distillation sources.",
        ),
        "updated_at": old_queue.get("updated_at", ""),
        "oracle_source_queue": {
            "enabled": use_oracle,
            "last_status": oracle_status,
            "updated_at": _now_iso(),
        },
        "candidates": _merge_candidates(
            old_queue.get("candidates", []),
            seeds + oracle_candidates,
        ),
    }
    changed = before != _json(_stable_for_compare(queue))
    if changed and not dry_run:
        write_queue(queue)
    return {
        "queue": queue,
        "changed": changed and not dry_run,
        "seed_count": len(seeds),
        "oracle_count": len(oracle_candidates),
        "oracle_status": oracle_status,
    }


def queue_counts(queue: dict[str, Any]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for item in queue.get("candidates", []):
        if not isinstance(item, dict):
            continue
        status = str(item.get("status", "unknown") or "unknown")
        counts[status] = counts.get(status, 0) + 1
    return counts


def format_queue_summary(queue: dict[str, Any], *, limit: int = 8) -> str:
    counts = queue_counts(queue)
    candidates = [
        item for item in queue.get("candidates", [])
        if isinstance(item, dict)
    ]
    lines = [
        "source queue:",
        "  " + ", ".join(f"{key}={value}" for key, value in sorted(counts.items()))
        if counts
        else "  empty",
    ]
    for item in candidates[:limit]:
        lines.append(
            "  - {status} p{priority}: {source} -> {sections}".format(
                status=item.get("status", "unknown"),
                priority=item.get("priority", 0),
                source=item.get("proposed_source", ""),
                sections=", ".join(distill._unique_strings(item.get("target_sections", []))),
            )
        )
    return "\n".join(lines)
