#!/usr/bin/env python3
"""Turn promising board candidates into target profiles.

Default mode is offline: list candidates that need profiles and optionally
write schema-valid stubs. LLM generation is explicit opt-in because it can spend
tokens and should not run just because the supervisor starts.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
LOG_DIR = SCRIPT_DIR / "outreach_state" / "profile_judge_logs"
OPERATOR_MEMORY_PATH = SCRIPT_DIR / "OPERATOR_MEMORY.md"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import parse_board  # noqa: E402
from outreach_preflight import NEEDS_PROFILE, NEEDS_BOARD_UPDATE, judge_board  # noqa: E402
from outreach_profile import SCHEMA_VERSION, validate_profile_dict, write_stub, profile_path_for_slug  # noqa: E402
from outreach_candidate_inbox import append_event, get_candidate, list_candidates  # noqa: E402


def _operator_memory() -> str:
    try:
        return OPERATOR_MEMORY_PATH.read_text(encoding="utf-8")
    except OSError:
        return "(operator memory unavailable)"


PROFILE_PROMPT = """You are designing a target-specific profile for the Omega outreach pipeline.

Operator memory:
```
{operator_memory}
```

The profile decides whether this candidate can enter automated deep reasoning.
Be strict: if the target is not a real open problem, output {{"verdict":"DROP","reason":"..."}}.
Also be strict about impact: if the target is merely a low-impact arXiv follow-up,
an author-email small question, or a derivative tweak inside someone else's paper,
DROP it unless the profile can name a broader theorem, reusable verifier,
classification, obstruction, or serious public artifact.

Output ONLY a JSON object. If viable, use this schema:

{{
  "verdict": "PROFILE",
  "profile": {{
    "schema_version": "{schema_version}",
    "todo_id": "{todo_id}",
    "slug": "{slug}",
    "title": {title_json},
    "source_url": {source_json},
    "profile_status": "ready",
    "final_display_form": "<concrete artifact + audience>",
    "success_gate": "<what must be true before user approval/send>",
    "no_external_send_without_operator_approval": true,
    "canonical_draft_paths": [
      "tools/community-outreach/targets/{slug}/research.md",
      "tools/community-outreach/targets/{slug}/submission_draft.md"
    ],
    "expected_artifacts": [
      "tools/community-outreach/targets/{slug}/research.md",
      "tools/community-outreach/targets/{slug}/results.json"
    ],
    "first_experiments": [
      {{
        "label": "<short>",
        "command": [],
        "expected_outputs": ["tools/community-outreach/targets/{slug}/research.md"],
        "success_predicate": "<checkable predicate>",
        "timeout_s": 1800
      }}
    ],
    "fallback_contribution": "<publishable/reportable fallback if full solution fails>",
    "science_contract": {{
      "contribution_type": "theorem|counterexample|construction|certificate|computational_record|source_audit_note|collaboration_packet|research_note",
      "target_lane": "math_lane|frontier_lane|collaboration_lane|audit_lane",
      "contract_quality_floor": 7,
      "origin": "ai",
      "closure_status": "seed",
      "verification_status": "unverified",
      "outreach_status": "not_drafted",
      "terminal_artifact": "tools/community-outreach/targets/{slug}/research.md",
      "verifier": "<exact proof/check/certificate condition that decides success>",
      "progress_metric": "<monotone metric the agent can improve each turn, e.g. conflict count, theorem gap count, certificate coverage, missing lemma count>",
      "taste_obligations": {{
        "novelty_witness": "<why this is not a stale/duplicate/renamed target; cite the concrete source/freshness distinction to verify>",
        "no_hidden_assumption_witness": "<what assumptions, data, external sources, and oracle knowledge are allowed; what is explicitly not allowed>",
        "reproducibility_witness": "<what artifact/check/certificate lets another reviewer reproduce or audit the claim>",
        "layer_separation_witness": "<how mathematical evidence, Automath/NewMath relation, draft text, and external send remain separate>"
      }},
      "evidence_required": [
        "<operator-reviewable evidence item 1>",
        "<operator-reviewable evidence item 2>"
      ],
      "writeback_when": [
        "<condition under which writeback/paper/email draft is justified>"
      ],
      "close_when": [
        "<condition under which target should be dropped, archived, or re-scoped>"
      ],
      "no_progress_patience_turns": 2
    }},
    "main_paper_bridge": {{
      "required_before_run": false,
      "section_hint": "",
      "omega_modules": [],
      "backflow_surface": "to be determined after progress"
    }},
    "oracle_judge_required": true,
    "freshness_required": true,
    "notes": "<short>"
  }}
}}

# Board entry

```
{raw_block}
```

# Rules

- Do not invent external facts.
- Prefer GitHub/arXiv/X/forum/blog/workshop source surfaces over closed registries.
- ArXiv is only an information source, not a priority signal. Recent arXiv small questions should not enter the board unless their topic impact is independently high.
- Prefer named conjectures, public verifier/certificate gaps, high-visibility specialist discussions, classification/rigidity/extremal problems, and targets that can become serious notes or papers.
- The profile is allowed to have no shell command if the first experiment is a proof-search/deep-reasoning task, but success_predicate must be concrete.
- The science_contract is mandatory. It must tell the agent what mathematical object ends the run and what evidence would verify it.
- Do not make "source audit only" the fallback for a high-priority math target unless the audit itself exposes a reproducibility-critical or community-visible gap.
- Set target_lane consistently: math_lane for proof/counterexample/construction/research-note targets, frontier_lane for computational certificate/search targets, collaboration_lane for email/thread collaboration packets, audit_lane for source-audit notes.
- contract_quality_floor is normally 7. Use 8 only for high-risk claims where the verifier and progress metric are exceptionally precise.
- Never set no_external_send_without_operator_approval to false.
- Do not include any field outside the schema.
"""


INBOX_PROFILE_PROMPT = """You are graduating an automatically discovered open-problem candidate into the Omega outreach pipeline.

Operator memory:
```
{operator_memory}
```

Be strict about freshness and public inspectability. If this is not a real, current, inspectable open problem, output {{"verdict":"DROP","reason":"..."}}.
Be strict about impact. If it is only a small recent arXiv follow-up or a likely
private author-email with little independent value, output DROP. The board should
prefer influential conjectures, public verifier gaps, reusable certificate
packages, classification/rigidity/extremal problems, and targets that could
become a serious paper, note, or public artifact.

Output ONLY a JSON object. If viable, use this schema:

{{
  "verdict": "PROFILE",
  "board": {{
    "title": "<short board title>",
    "source_url": {source_json},
    "type": "<open problem / author question / issue / arxiv followup>",
    "untouched": "<specific freshness/currentness evidence or what must be checked>",
    "fit_score": <0-10>,
    "topic_score": <0-10>,
    "effort_estimate_days": "<number or range>",
    "risk": "low|med|high",
    "final_display": "<concrete artifact + audience>",
    "success_gate": "<what must be true before operator approval/send>",
    "statement": "<precise mathematical statement>",
    "prior": "<freshness/literature baseline; include dates/sources if known>",
    "omega_fit_detail": "<specific fit to automath/Omega tools, or explain exploratory bridge>",
    "attack_plan": ["<step 1>", "<step 2>", "<step 3>"],
    "rationale": "<why this should enter the board>"
  }},
  "profile": {{
    "schema_version": "{schema_version}",
    "todo_id": "__TODO_ID__",
    "slug": "__SLUG__",
    "title": "<same as board title>",
    "source_url": {source_json},
    "profile_status": "ready",
    "final_display_form": "<same as board.final_display>",
    "success_gate": "<same as board.success_gate>",
    "no_external_send_without_operator_approval": true,
    "canonical_draft_paths": [
      "tools/community-outreach/targets/__SLUG__/research.md",
      "tools/community-outreach/targets/__SLUG__/submission_draft.md"
    ],
    "expected_artifacts": [
      "tools/community-outreach/targets/__SLUG__/research.md",
      "tools/community-outreach/targets/__SLUG__/results.json"
    ],
    "first_experiments": [
      {{
        "label": "<short>",
        "command": [],
        "expected_outputs": ["tools/community-outreach/targets/__SLUG__/research.md"],
        "success_predicate": "<checkable predicate>",
        "timeout_s": 1800
      }}
    ],
    "fallback_contribution": "<publishable/reportable fallback if full solution fails>",
    "science_contract": {{
      "contribution_type": "theorem|counterexample|construction|certificate|computational_record|source_audit_note|collaboration_packet|research_note",
      "target_lane": "math_lane|frontier_lane|collaboration_lane|audit_lane",
      "contract_quality_floor": 7,
      "origin": "inbox",
      "closure_status": "seed",
      "verification_status": "unverified",
      "outreach_status": "not_drafted",
      "terminal_artifact": "tools/community-outreach/targets/__SLUG__/research.md",
      "verifier": "<exact proof/check/certificate condition that decides success>",
      "progress_metric": "<monotone metric the agent can improve each turn, e.g. conflict count, theorem gap count, certificate coverage, missing lemma count>",
      "taste_obligations": {{
        "novelty_witness": "<why this is not a stale/duplicate/renamed target; cite the concrete source/freshness distinction to verify>",
        "no_hidden_assumption_witness": "<what assumptions, data, external sources, and oracle knowledge are allowed; what is explicitly not allowed>",
        "reproducibility_witness": "<what artifact/check/certificate lets another reviewer reproduce or audit the claim>",
        "layer_separation_witness": "<how mathematical evidence, Automath/NewMath relation, draft text, and external send remain separate>"
      }},
      "evidence_required": [
        "<operator-reviewable evidence item 1>",
        "<operator-reviewable evidence item 2>"
      ],
      "writeback_when": [
        "<condition under which writeback/paper/email draft is justified>"
      ],
      "close_when": [
        "<condition under which target should be dropped, archived, or re-scoped>"
      ],
      "no_progress_patience_turns": 2
    }},
    "main_paper_bridge": {{
      "required_before_run": false,
      "section_hint": "",
      "omega_modules": [],
      "backflow_surface": "to be determined after progress"
    }},
    "oracle_judge_required": true,
    "freshness_required": true,
    "notes": "<short>"
  }}
}}

# Candidate inbox row

```json
{candidate_json}
```

# Existing board titles and sources

```json
{existing_json}
```

# Rules

- Do not invent external facts. If freshness cannot be responsibly bounded, DROP or set a concrete prior/freshness check in board.prior.
- Prefer GitHub/arXiv/X/forum/blog/workshop source surfaces with inspectable URLs.
- ArXiv is only an information source, not a priority signal. Do not graduate low-impact arXiv-derived email tasks unless they have exceptional topic value or a reusable certificate/theorem package.
- Every viable candidate must have a final display form and success gate.
- Every viable candidate must have a science_contract with an explicit terminal artifact, verifier, progress metric, writeback condition, and close condition.
- Do not make "source audit only" the fallback unless the audit itself has community-visible value.
- Set target_lane consistently: math_lane for proof/counterexample/construction/research-note targets, frontier_lane for computational certificate/search targets, collaboration_lane for email/thread collaboration packets, audit_lane for source-audit notes.
- contract_quality_floor is normally 7. Use 8 only for high-risk claims where the verifier and progress metric are exceptionally precise.
- Never set no_external_send_without_operator_approval to false.
- Use "__TODO_ID__" and "__SLUG__" placeholders exactly in profile paths; the Python wrapper will replace them.
- Do not include any field outside the schema.
"""


def _slugify_candidate(title: str, source_url: str = "") -> str:
    haystack = f"{source_url} {title}"
    m = re.search(r"arxiv\.org/abs/(\d{4}\.\d{4,6})", haystack, re.IGNORECASE)
    if not m:
        m = re.search(r"arxiv:(\d{4}\.\d{4,6})", haystack, re.IGNORECASE)
    if m:
        return "arxiv_" + m.group(1).replace(".", "_")
    m = re.search(r"github\.com/([^/\s]+)/([^/\s]+)/issues/(\d+)", source_url, re.IGNORECASE)
    if m:
        owner = re.sub(r"[^a-z0-9]+", "_", m.group(1).lower()).strip("_")[:12]
        repo = re.sub(r"[^a-z0-9]+", "_", m.group(2).lower()).strip("_")[:14]
        return f"github_{owner}_{repo}_{m.group(3)}"[:48]
    words = [w.lower() for w in re.findall(r"[A-Za-z0-9]{3,}", title)][:5]
    return ("cand_" + "_".join(words))[:48] if words else "candidate"


def _unique_slug(base: str) -> str:
    slug = re.sub(r"[^a-z0-9_]+", "_", base.lower()).strip("_")[:48] or "candidate"
    existing_slugs = {todo.slug() for todo in parse_board(BOARD_PATH).values()}
    if slug not in existing_slugs and not profile_path_for_slug(slug).exists():
        return slug
    for i in range(2, 100):
        cand = f"{slug[:42]}_{i}"
        if cand not in existing_slugs and not profile_path_for_slug(cand).exists():
            return cand
    raise RuntimeError(f"could not allocate unique slug for {base}")


def _next_todo_id() -> str:
    nums: list[int] = []
    for tid in parse_board(BOARD_PATH):
        m = re.match(r"^T-(\d+)$", tid)
        if m:
            nums.append(int(m.group(1)))
    return f"T-{(max(nums) + 1) if nums else 1:02d}"


def _existing_board_summary() -> list[dict]:
    out = []
    for todo in parse_board(BOARD_PATH).values():
        out.append({
            "todo_id": todo.todo_id,
            "title": todo.title,
            "source": todo.source,
            "slug": todo.slug(),
            "status": todo.status,
        })
    return out[-80:]


def _format_board_from_judge(todo_id: str, board: dict, slug: str = "") -> str:
    attack_plan = board.get("attack_plan") or []
    if not isinstance(attack_plan, list):
        attack_plan = [str(attack_plan)]
    attack = "\n".join(f"{i + 1}. {str(step).strip()}" for i, step in enumerate(attack_plan) if str(step).strip())
    if not attack:
        attack = "1. Build target profile and run freshness/deep judge."
    slug = str(slug or "").strip()
    deliverables = []
    if slug:
        deliverables = [
            f"- tools/community-outreach/targets/{slug}/research.md",
            f"- tools/community-outreach/targets/{slug}/results.json",
            f"- tools/community-outreach/targets/{slug}/submission_draft.md",
        ]
    return "\n".join([
        f"### {todo_id} · {str(board.get('title') or 'Untitled candidate').strip()}",
        "",
        "| field | value |",
        "|---|---|",
        "| Status | Backlog (candidate inbox graduation) |",
        f"| Source | {str(board.get('source_url') or '').strip()} |",
        f"| Type | {str(board.get('type') or 'open problem').strip()} |",
        f"| Untouched | {str(board.get('untouched') or '?').strip()} |",
        f"| Omega fit | {int(board.get('fit_score') or 0)}/10 |",
        f"| Topic value | {int(board.get('topic_score') or 0)}/10 |",
        f"| Effort est | {str(board.get('effort_estimate_days') or '?').strip()} 天 |",
        f"| Risk | {str(board.get('risk') or 'med').strip()} |",
        f"| Final display | {str(board.get('final_display') or '').strip()} |",
        f"| Success gate | {str(board.get('success_gate') or '').strip()} |",
        "",
        f"**Statement.** {str(board.get('statement') or '').strip()}",
        "",
        f"**Prior.** {str(board.get('prior') or '').strip()}",
        "",
        f"**Omega fit detail.** {str(board.get('omega_fit_detail') or '').strip()}",
        "",
        f"**Attack plan.**\n{attack}",
        "",
        "**Deliverables.**\n" + ("\n".join(deliverables) if deliverables else "同模板."),
        "",
        f"_Inbox graduation rationale_: {str(board.get('rationale') or '').strip()}",
        "",
        "---",
        "",
    ])


def _append_board_block(block: str) -> None:
    text = BOARD_PATH.read_text(encoding="utf-8") if BOARD_PATH.exists() else ""
    if text and not text.endswith("\n"):
        text += "\n"
    tmp = BOARD_PATH.with_suffix(".md.tmp")
    tmp.write_text(text + "\n" + block, encoding="utf-8")
    tmp.replace(BOARD_PATH)


def _extract_agent_messages_from_jsonl(text: str) -> list[str]:
    messages: list[str] = []
    for line in (text or "").splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if obj.get("type") != "item.completed":
            continue
        item = obj.get("item") or {}
        if item.get("type") == "agent_message" and isinstance(item.get("text"), str):
            messages.append(item["text"])
    return messages


def _extract_json(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    agent_messages = _extract_agent_messages_from_jsonl(text)
    for msg in reversed(agent_messages):
        obj = _extract_json(msg)
        if obj:
            return obj
    fence = re.search(r"```(?:json)?\s*(.*?)\s*```", text, re.DOTALL)
    candidates = []
    if fence:
        candidates.append(fence.group(1).strip())
    first = text.find("{")
    last = text.rfind("}")
    if first >= 0 and last > first:
        candidates.append(text[first:last + 1])
    for candidate in candidates:
        try:
            obj = json.loads(candidate)
            return obj if isinstance(obj, dict) else None
        except json.JSONDecodeError:
            continue
    decoder = json.JSONDecoder()
    for i, ch in enumerate(text):
        if ch != "{":
            continue
        try:
            obj, _ = decoder.raw_decode(text[i:])
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            return obj
    return None


def _mark_board_status(todo_id: str, status: str, note: str = "") -> bool:
    """Conservatively update only the Status row of a T-NN block."""
    if not BOARD_PATH.exists():
        return False
    text = BOARD_PATH.read_text(encoding="utf-8")
    header = re.search(rf"^### {re.escape(todo_id)}\s*[··]\s*.*$", text, re.MULTILINE)
    if not header:
        return False
    next_header = re.search(r"^### T-\d+\s*[··]\s*.*$", text[header.end():], re.MULTILINE)
    end = header.end() + next_header.start() if next_header else len(text)
    block = text[header.start():end]
    safe_note = note.replace("|", "/").replace("\n", " ").strip()[:220]
    value = f"**🔴 DROP · profile judge {status}**"
    if safe_note:
        value += f" — {safe_note}"
    new_block, n = re.subn(
        r"^\|\s*Status\s*\|\s*.*?\s*\|$",
        f"| Status | {value} |",
        block,
        count=1,
        flags=re.MULTILINE,
    )
    if n != 1:
        return False
    tmp = BOARD_PATH.with_suffix(".md.tmp")
    tmp.write_text(text[:header.start()] + new_block + text[end:], encoding="utf-8")
    tmp.replace(BOARD_PATH)
    return True


def select_candidates(*, top: int, min_score: int) -> list[dict]:
    todos = parse_board(BOARD_PATH)
    verdicts = judge_board()
    out: list[dict] = []
    for v in verdicts:
        if v.verdict not in {NEEDS_PROFILE, NEEDS_BOARD_UPDATE}:
            continue
        if v.verdict == NEEDS_BOARD_UPDATE and not any(
            "profile" in m.lower() or "science_contract" in m.lower()
            for m in v.missing
        ):
            continue
        if v.score < min_score:
            continue
        todo = todos.get(v.todo_id)
        if not todo:
            continue
        out.append({
            "todo_id": v.todo_id,
            "slug": v.slug,
            "title": v.title,
            "score": v.score,
            "verdict": v.verdict,
            "missing": v.missing,
        })
        if len(out) >= top:
            break
    return out


def generate_with_codex(todo_id: str) -> tuple[bool, str]:
    todos = parse_board(BOARD_PATH)
    todo = todos.get(todo_id)
    if not todo:
        return False, f"{todo_id} not found"
    slug = todo.slug()
    prompt = PROFILE_PROMPT.format(
        operator_memory=_operator_memory()[:12000],
        schema_version=SCHEMA_VERSION,
        todo_id=todo.todo_id,
        slug=slug,
        title_json=json.dumps(todo.title, ensure_ascii=False),
        source_json=json.dumps(todo.source, ensure_ascii=False),
        raw_block=todo.raw_block[:20000],
    )
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    prompt_path = LOG_DIR / f"{todo_id}_profile_prompt.txt"
    stdout_path = LOG_DIR / f"{todo_id}_profile_stdout.txt"
    prompt_path.write_text(prompt, encoding="utf-8")
    cmd = ["/opt/homebrew/bin/codex", "exec", "--json", "--skip-git-repo-check"]
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            input=prompt,
            capture_output=True,
            text=True,
            timeout=1800,
        )
    except Exception as exc:
        return False, f"codex spawn failed: {exc}"
    stdout_path.write_text(proc.stdout or "", encoding="utf-8")
    if proc.returncode != 0:
        return False, f"codex rc={proc.returncode}: {(proc.stderr or proc.stdout)[:400]}"
    obj = _extract_json(proc.stdout)
    if not obj:
        return False, "could not parse JSON from codex output"
    if obj.get("verdict") != "PROFILE":
        verdict = str(obj.get("verdict") or "")
        reason = str(obj.get("reason") or "")
        if verdict == "DROP":
            changed = _mark_board_status(todo_id, "DROP", reason)
            return False, f"codex verdict=DROP board_marked={changed}: {reason}"
        return False, f"codex verdict={obj.get('verdict')}: {reason}"
    profile = obj.get("profile")
    if not isinstance(profile, dict):
        return False, "profile missing or not object"
    if profile.get("slug") != slug:
        return False, (
            f"profile slug mismatch: {profile.get('slug')!r} != board slug {slug!r}; "
            "candidate needs board rewrite/graduation, not direct profile"
        )
    errors = validate_profile_dict(profile)
    if errors:
        return False, "profile validation failed: " + "; ".join(errors)
    path = profile_path_for_slug(slug)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(profile, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return True, str(path.relative_to(SCRIPT_DIR))


def generate_board_batch_with_codex(*, top: int, min_score: int) -> dict:
    rows = select_candidates(top=top, min_score=min_score)
    results = []
    for row in rows:
        ok, msg = generate_with_codex(row["todo_id"])
        results.append({
            "todo_id": row["todo_id"],
            "slug": row["slug"],
            "ok": ok,
            "message": msg,
        })
    return {"processed": len(results), "results": results}


def select_inbox_candidates(*, top: int) -> list[dict]:
    rows = []
    for r in list_candidates():
        status = r.get("status")
        if status == "needs_profile_judge":
            rows.append(r)
            continue
        if status == "profile_failed":
            note = str(r.get("note") or "")
            if "validation failed" in note:
                rows.append(r)
    rows.sort(key=lambda r: r.get("received_at_epoch") or 0)
    return rows[:top]


def graduate_inbox_with_codex(candidate_id: str) -> tuple[bool, str]:
    row = get_candidate(candidate_id)
    if not row:
        return False, f"candidate {candidate_id} not found"
    status = row.get("status")
    if status not in {"needs_profile_judge", "profile_failed"}:
        return False, f"candidate {candidate_id} status={status} is not profileable"
    if status == "profile_failed" and "validation failed" not in str(row.get("note") or ""):
        return False, f"candidate {candidate_id} profile_failed for non-validation reason; not auto-retrying"
    candidate = row.get("candidate") or {}
    source_url = str(candidate.get("source_url") or "")
    prompt = INBOX_PROFILE_PROMPT.format(
        operator_memory=_operator_memory()[:12000],
        schema_version=SCHEMA_VERSION,
        source_json=json.dumps(source_url, ensure_ascii=False),
        candidate_json=json.dumps(row, ensure_ascii=False, indent=2),
        existing_json=json.dumps(_existing_board_summary(), ensure_ascii=False, indent=2),
    )
    if status == "profile_failed":
        prompt += (
            "\n\n# Previous validation failure to repair\n\n"
            + str(row.get("note") or "")
            + "\n\nRegenerate the board/profile JSON so these validation errors are fixed exactly. "
              "Do not use placeholder-like taste witnesses; make no_hidden_assumption_witness and "
              "reproducibility_witness concrete, source-bounded, and auditable.\n"
        )
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    prompt_path = LOG_DIR / f"inbox_{candidate_id}_profile_prompt.txt"
    stdout_path = LOG_DIR / f"inbox_{candidate_id}_profile_stdout.txt"
    prompt_path.write_text(prompt, encoding="utf-8")
    cmd = ["/opt/homebrew/bin/codex", "exec", "--json", "--skip-git-repo-check"]
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            input=prompt,
            capture_output=True,
            text=True,
            timeout=1800,
        )
    except Exception as exc:
        append_event(candidate_id, status="profile_failed", note=f"codex spawn failed: {exc}")
        return False, f"codex spawn failed: {exc}"
    stdout_path.write_text(proc.stdout or "", encoding="utf-8")
    if proc.returncode != 0:
        msg = f"codex rc={proc.returncode}: {(proc.stderr or proc.stdout)[:400]}"
        append_event(candidate_id, status="profile_failed", note=msg)
        return False, msg
    obj = _extract_json(proc.stdout)
    if not obj:
        append_event(candidate_id, status="profile_failed", note="could not parse JSON from codex output")
        return False, "could not parse JSON from codex output"
    if obj.get("verdict") != "PROFILE":
        reason = str(obj.get("reason") or "")
        append_event(candidate_id, status="dropped", note=f"judge verdict={obj.get('verdict')}: {reason}")
        return False, f"judge verdict={obj.get('verdict')}: {reason}"
    board = obj.get("board")
    profile = obj.get("profile")
    if not isinstance(board, dict) or not isinstance(profile, dict):
        append_event(candidate_id, status="profile_failed", note="board/profile missing or not object")
        return False, "board/profile missing or not object"
    todo_id = _next_todo_id()
    title = str(board.get("title") or profile.get("title") or candidate.get("title") or "")
    slug = _unique_slug(_slugify_candidate(title, source_url))
    for key, value in {
        "todo_id": todo_id,
        "slug": slug,
        "title": title,
        "source_url": source_url,
    }.items():
        profile[key] = value
    profile["schema_version"] = SCHEMA_VERSION
    profile["profile_status"] = "ready"
    profile["no_external_send_without_operator_approval"] = True
    profile["canonical_draft_paths"] = [
        str(p).replace("__SLUG__", slug) for p in profile.get("canonical_draft_paths", [])
    ] or [
        f"tools/community-outreach/targets/{slug}/research.md",
        f"tools/community-outreach/targets/{slug}/submission_draft.md",
    ]
    profile["expected_artifacts"] = [
        str(p).replace("__SLUG__", slug) for p in profile.get("expected_artifacts", [])
    ] or [
        f"tools/community-outreach/targets/{slug}/research.md",
        f"tools/community-outreach/targets/{slug}/results.json",
    ]
    for exp in profile.get("first_experiments") or []:
        if isinstance(exp, dict):
            exp["expected_outputs"] = [
                str(p).replace("__SLUG__", slug) for p in (exp.get("expected_outputs") or [])
            ]
    science_contract = profile.get("science_contract")
    if isinstance(science_contract, dict):
        science_contract["terminal_artifact"] = str(
            science_contract.get("terminal_artifact") or ""
        ).replace("__SLUG__", slug)
    errors = validate_profile_dict(profile)
    required_board = [
        "title", "source_url", "final_display", "success_gate", "statement",
        "prior", "omega_fit_detail", "attack_plan",
    ]
    for key in required_board:
        if not board.get(key):
            errors.append(f"board missing {key}")
    if errors:
        msg = "validation failed: " + "; ".join(errors)
        append_event(candidate_id, status="profile_failed", note=msg)
        return False, msg
    profile_path = profile_path_for_slug(slug)
    profile_path.parent.mkdir(parents=True, exist_ok=True)
    profile_path.write_text(json.dumps(profile, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    _append_board_block(_format_board_from_judge(todo_id, board, slug))
    append_event(
        candidate_id,
        status="graduated",
        note=f"graduated to {todo_id} {slug}",
        metadata={
            "todo_id": todo_id,
            "slug": slug,
            "profile_path": str(profile_path.relative_to(SCRIPT_DIR)),
        },
    )
    return True, f"graduated {candidate_id} -> {todo_id} {slug}"


def graduate_inbox_batch(*, top: int) -> dict:
    rows = select_inbox_candidates(top=top)
    results = []
    for row in rows:
        cid = str(row.get("candidate_id") or "")
        ok, msg = graduate_inbox_with_codex(cid)
        results.append({"candidate_id": cid, "ok": ok, "message": msg})
    return {"processed": len(results), "results": results}


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--top", type=int, default=8)
    p.add_argument("--min-score", type=int, default=12)
    p.add_argument("--todo-id", default="")
    p.add_argument("--candidate-id", default="")
    p.add_argument("--write-stub", action="store_true", help="write schema-valid placeholder profile(s)")
    p.add_argument("--generate-with-codex", action="store_true", help="spend tokens to ask Codex for profile JSON")
    p.add_argument("--generate-board-batch-with-codex", action="store_true",
                   help="spend tokens to generate profiles for top board NEEDS_PROFILE entries")
    p.add_argument("--graduate-inbox-with-codex", action="store_true",
                   help="spend tokens to graduate candidate_inbox row(s) to board/profile")
    p.add_argument("--force", action="store_true")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)

    if args.graduate_inbox_with_codex:
        if args.candidate_id:
            ok, msg = graduate_inbox_with_codex(args.candidate_id)
            print(json.dumps({"ok": ok, "message": msg}, ensure_ascii=False, indent=2))
            return 0 if ok else 1
        payload = graduate_inbox_batch(top=args.top)
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0 if all(r.get("ok") for r in payload["results"]) else 1

    if args.generate_board_batch_with_codex:
        payload = generate_board_batch_with_codex(top=args.top, min_score=args.min_score)
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0 if all(r.get("ok") for r in payload["results"]) else 1

    if args.generate_with_codex:
        if not args.todo_id:
            p.error("--generate-with-codex requires --todo-id")
        ok, msg = generate_with_codex(args.todo_id)
        print(json.dumps({"ok": ok, "message": msg}, ensure_ascii=False, indent=2))
        return 0 if ok else 1

    if args.todo_id and args.write_stub:
        path = write_stub(args.todo_id, force=args.force)
        print(str(path.relative_to(SCRIPT_DIR)))
        return 0

    candidates = select_candidates(top=args.top, min_score=args.min_score)
    inbox_candidates = select_inbox_candidates(top=args.top)
    if args.write_stub:
        written = []
        for c in candidates:
            path = write_stub(c["todo_id"], force=args.force)
            written.append(str(path.relative_to(SCRIPT_DIR)))
        payload = {"candidates": candidates, "inbox_candidates": inbox_candidates, "written": written}
    else:
        payload = {"candidates": candidates, "inbox_candidates": inbox_candidates}

    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for c in candidates:
            print(f"{c['todo_id']} score={c['score']} {c['verdict']} {c['slug']} :: {c['title']}")
            if c["missing"]:
                print("  missing: " + "; ".join(c["missing"]))
        if inbox_candidates:
            print("Inbox candidates:")
            for row in inbox_candidates:
                cand = row.get("candidate") or {}
                print(f"{row.get('candidate_id')} {row.get('source')} :: {cand.get('title')}")
        if args.write_stub:
            for pth in payload["written"]:
                print(f"wrote {pth}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
