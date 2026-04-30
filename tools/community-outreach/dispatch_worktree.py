#!/usr/bin/env python3
"""dispatch_worktree.py — bridge between RESEARCH_BOARD.md and the outreach orchestrator.

Designed as a stable interface for the outreach pipeline (and codex-driven plumbing
on top of it) to:
  1. Parse RESEARCH_BOARD.md into structured TodoSpec records.
  2. Build a self-contained agent prompt for Stage A (research.md drafting).
  3. Optionally create an isolated git worktree on a per-target branch.
  4. Optionally seed the per-target outreach_state JSON.
  5. Supervise selected RESEARCH_BOARD targets by rerunning safe local
     experiments, writing ignored logs/state, and stopping before any external
     submission gate.

Public API (importable):
    parse_board(path) -> dict[str, TodoSpec]
    plan_dispatch(todo_id, *, board_path, repo_root, ...) -> DispatchPlan
    create_worktree(plan) -> Path
    seed_state_json(plan) -> Path

CLI:
    dispatch_worktree.py --list
    dispatch_worktree.py [--json] T-NN
    dispatch_worktree.py --create [--seed-state] T-NN
    dispatch_worktree.py --create --worktree-root /tmp/wt T-NN
    dispatch_worktree.py --supervise --supervise-id T-01 --supervise-id T-02 --supervise-id T-08 --run

Hard rules enforced (matches CLAUDE.md + memory):
  - Never touches lean4/ except as static read input
  - Never auto-commits, never pushes
  - Never invokes external submission channels (gh / mail / curl POST)
  - Stage A stops at research.md + state JSON update; Stage B onward is the
    orchestrator's responsibility, NOT this script
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
BOARD_PATH_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/RESEARCH_BOARD.md"
STATE_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/outreach_state"
TARGETS_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/targets"
LOGS_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/logs"
WORKTREE_ROOT_DEFAULT = REPO_ROOT_DEFAULT.parent / "_outreach_worktrees"
SCHEMA_VERSION = "community-outreach-state-v3-research-board"
SUPERVISOR_SCHEMA_VERSION = "community-outreach-supervisor-v1"

# Compatibility aliases for targets that were already researched before the
# generic board slugger existed. Keep these stable so reruns reuse the existing
# ignored target directories rather than silently forking evidence.
TARGET_SLUG_OVERRIDES = {
    "T-08": "opg_lucas_mod_m",
}


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class TodoSpec:
    todo_id: str
    title: str
    status: str
    source: str
    type_: str
    untouched: str
    fit_score: int | None
    topic_score: int | None
    effort: str
    risk: str
    statement: str
    prior: str
    omega_fit_detail: str
    attack_plan: list[str]
    worktree_inputs: list[str]
    deliverables: list[str]
    raw_block: str

    def slug(self) -> str:
        # 0. TARGET_SLUG_OVERRIDES wins (compatibility with pre-existing target dirs)
        if self.todo_id in TARGET_SLUG_OVERRIDES:
            return TARGET_SLUG_OVERRIDES[self.todo_id]
        # 1. Explicit override in table
        # 2. targets/<slug>/ in deliverables
        for d in self.deliverables:
            m = re.search(r"targets/([a-z0-9_]+)/", d.lower())
            if m:
                return m.group(1)
        # 3. Erdős #N pattern in title → erdos_N
        m = re.search(r"Erd[őo]?s\s*#?(\d+)", self.title)
        if m:
            return f"erdos_{m.group(1)}"
        # 4. arxiv ID in source or title (strip vN suffix). Try URL then inline.
        haystack = self.source + " " + self.title
        m = re.search(r"arxiv\.org/abs/(\d{4}\.\d{4,6})", haystack, re.IGNORECASE)
        if not m:
            m = re.search(r"arxiv:(\d{4}\.\d{4,6})", haystack, re.IGNORECASE)
        if m:
            return "arxiv_" + m.group(1).replace(".", "_")
        # 5. AimPL workshop → aimpl_<name>
        m = re.search(r"aimpl\.org/([a-z0-9]+)", self.source)
        if m:
            return f"aimpl_{m.group(1)}"
        # 6. OPG → opg_<name>
        m = re.search(r"openproblemgarden\.org/op/([a-z0-9_]+)", self.source)
        if m:
            return f"opg_{m.group(1)[:24]}"
        # 7. Tao blog → tao_<first-2-words>
        m = re.search(r"terrytao\.wordpress\.com/[\d/]+/([a-z0-9-]+)", self.source)
        if m:
            parts = [p for p in m.group(1).split("-") if p][:2]
            return "tao_" + "_".join(parts) if parts else "tao_post"
        # 8. erdosproblems.com/N → erdos_N
        m = re.search(r"erdosproblems\.com/(\d+)", self.source)
        if m:
            return f"erdos_{m.group(1)}"
        # 9. Fallback: title first 2-3 alphabetic words, max 32
        words = [w.lower() for w in re.findall(r"[A-Za-z]{3,}", self.title)][:3]
        base = "_".join(words)[:32]
        return base or self.todo_id.replace("-", "_").lower()

    def expanded_deliverables(self) -> list[str]:
        """Resolve '同模板' shorthand into concrete paths based on slug."""
        if not self.deliverables or any("同模板" in d for d in self.deliverables):
            slug = self.slug()
            area = slug.split("_", 1)[0]  # erdos, arxiv, tao, aimpl, opg
            return [
                f"tools/community-outreach/targets/{slug}/research.md",
                f"tools/community-outreach/{area}/{slug}_*.py",
                f"tools/community-outreach/targets/{slug}/submission_draft.md",
                f"theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/{slug}/main.tex",
            ]
        return list(self.deliverables)

    def submission_target(self) -> dict[str, str]:
        s = self.source
        if "erdosproblems.com/forum" in s:
            return {"type": "forum_post", "venue": "erdosproblems.com forum", "format": "markdown"}
        if "erdosproblems.com/" in s:
            return {"type": "forum_comment", "venue": "erdosproblems.com problem page", "format": "markdown"}
        if "github.com/teorth/erdosproblems" in s:
            return {"type": "github_pr", "venue": "teorth/erdosproblems data/problems.yaml", "format": "yaml_diff"}
        if "arxiv.org" in s:
            return {"type": "arxiv_followup", "venue": "arXiv preprint or author email", "format": "tex_or_email"}
        if "terrytao.wordpress.com" in s:
            return {"type": "blog_comment", "venue": "Tao blog comment", "format": "markdown"}
        if "aimpl.org" in s:
            return {"type": "email_authors", "venue": "AimPL workshop email", "format": "markdown_or_pdf"}
        if "openproblemgarden.org" in s:
            return {"type": "comment_or_email", "venue": "OPG comment + author email", "format": "markdown"}
        return {"type": "unknown", "venue": s, "format": "markdown"}


@dataclass
class DispatchPlan:
    todo: TodoSpec
    repo_root: Path
    branch: str
    worktree_path: Path
    target_dir_in_worktree: Path
    state_json_path: Path
    research_md_path: Path
    agent_prompt: str
    submission_target: dict[str, str]

    def to_serializable(self) -> dict:
        d = {
            "todo": asdict(self.todo),
            "repo_root": str(self.repo_root),
            "branch": self.branch,
            "worktree_path": str(self.worktree_path),
            "target_dir_in_worktree": str(self.target_dir_in_worktree),
            "state_json_path": str(self.state_json_path),
            "research_md_path": str(self.research_md_path),
            "submission_target": self.submission_target,
            "agent_prompt": self.agent_prompt,
        }
        return d


# ---------------------------------------------------------------------------
# Board parser
# ---------------------------------------------------------------------------


_TODO_HEADER = re.compile(r"^### (T-\d+)\s*[··]\s*(.+)$", re.MULTILINE)
_TABLE_ROW = re.compile(r"^\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*$", re.MULTILINE)
_SCORE = re.compile(r"(\d+)\s*/\s*10")


def _split_blocks(text: str) -> list[tuple[str, str, str]]:
    """Split board text into (todo_id, title, body) per TODO."""
    matches = list(_TODO_HEADER.finditer(text))
    blocks = []
    for i, m in enumerate(matches):
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end]
        blocks.append((m.group(1), m.group(2).strip(), body))
    return blocks


def _extract_table(body: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for m in _TABLE_ROW.finditer(body):
        k = m.group(1).strip().lower()
        v = m.group(2).strip()
        if k in {"field", "---"} or v in {"value", "---"}:
            continue
        fields[k] = v
    return fields


def _extract_section(body: str, label: str) -> str:
    """Extract a labelled paragraph or list. label is e.g. 'Statement', 'Prior'."""
    pattern = re.compile(
        r"\*\*" + re.escape(label) + r"\.?\*\*\s*\n?(.*?)(?=\n\*\*[A-Z]|\n---|\Z)",
        re.DOTALL,
    )
    m = pattern.search(body)
    return m.group(1).strip() if m else ""


def _extract_numbered_steps(body: str, label: str) -> list[str]:
    sect = _extract_section(body, label)
    steps: list[str] = []
    for line in sect.splitlines():
        line = line.strip()
        m = re.match(r"^\d+\.\s*(.+)$", line)
        if m:
            steps.append(m.group(1).strip())
    return steps


def _extract_bullets(body: str, label: str) -> list[str]:
    sect = _extract_section(body, label)
    bullets: list[str] = []
    for line in sect.splitlines():
        line = line.strip()
        m = re.match(r"^[-*]\s*(.+)$", line)
        if m:
            bullets.append(m.group(1).strip())
    if not bullets and sect:
        # Fallback: comma / period split for inline lists
        for chunk in re.split(r"[,;]\s*", sect):
            chunk = chunk.strip().strip("`").strip()
            if chunk:
                bullets.append(chunk)
    return bullets


def _score_from_field(text: str) -> int | None:
    m = _SCORE.search(text or "")
    return int(m.group(1)) if m else None


def parse_board(path: Path) -> dict[str, TodoSpec]:
    text = path.read_text(encoding="utf-8")
    todos: dict[str, TodoSpec] = {}
    for todo_id, title, body in _split_blocks(text):
        table = _extract_table(body)
        spec = TodoSpec(
            todo_id=todo_id,
            title=title,
            status=table.get("status", ""),
            source=table.get("source", ""),
            type_=table.get("type", ""),
            untouched=table.get("untouched", ""),
            fit_score=_score_from_field(table.get("omega fit", "")),
            topic_score=_score_from_field(table.get("topic value", "")),
            effort=table.get("effort est", ""),
            risk=table.get("risk", ""),
            statement=_extract_section(body, "Statement"),
            prior=_extract_section(body, "Prior"),
            omega_fit_detail=_extract_section(body, "Omega fit detail"),
            attack_plan=_extract_numbered_steps(body, "Attack plan"),
            worktree_inputs=_extract_bullets(body, "Worktree-ready inputs"),
            deliverables=_extract_bullets(body, "Deliverables"),
            raw_block=body.strip(),
        )
        todos[todo_id] = spec
    return todos


# ---------------------------------------------------------------------------
# Agent prompt template
# ---------------------------------------------------------------------------


_AGENT_PROMPT = """你是 Omega 数学项目的 community-outreach Stage A 调研者, 已被派进独立 git worktree.

## TODO 信息

ID: {todo_id}
标题: {title}
来源: {source}
类型: {type_}
Omega fit: {fit_score}/10
Topic value: {topic_score}/10
Effort 估计: {effort}
Risk: {risk}
Untouched 证据: {untouched}

## 数学问题陈述

{statement}

## 已知 prior work

{prior}

## Omega 库对位机器

{omega_fit_detail}

## 看板建议的 attack plan

{attack_plan_block}

## 期望 deliverables (Stage A 只产出 research.md, 其他在后续 Stage)

{deliverables_block}

## 静态可读输入 (不要编辑这些文件, 只读)

{worktree_inputs_block}

## 提交目标 (Stage E 才动, 现在不接触)

类型: {submission_type}
渠道: {submission_venue}
格式: {submission_format}

## 你的工作 (Stage A)

1. 读 RESEARCH_BOARD.md 中本 TODO 完整定义
2. 读相关 lean4/Omega 模块 (静态读取, 不编辑)
3. 以中文起草 `{research_md_relpath}`, 至少包含:
   - 题面精确陈述 (LaTeX 数学公式)
   - 已知 prior work 整理 (含原始论文链接)
   - 攻击思路展开 (在看板 attack plan 之上做更细的分解)
   - 所需 lean4/Omega 库引理清单 (给文件路径与 lemma 名)
   - 第一步具体动作 plan (写什么脚本 / 验什么参数空间 / 证什么 lemma)
   - 风险与失败时的 fallback contribution (即便不全证, 哪些数据/部分结果可发表)
4. 完成 research.md 后**停下**, 等用户审; 不要进 Stage B (草稿) 或 Stage C (双审)

## 硬约束 (违反即失败)

- **NO_LEAN_EXECUTION_POLICY**: 不跑 lake/lean/elan/#eval/#check, 也不编辑 `lean4/` 下任何文件
- 不接触 `tools/community-outreach/outreach_state/*.json` (orchestrator 责任)
- 不修改其他 worktree 的文件
- 不自动 git commit / push
- 不发任何外部内容 (无 gh / mail / curl POST)
- 中文输出 deliverable, 按 `BACKFLOW_LANGUAGE_POLICY`
- 不引入未必要的库依赖, 也不安装新 package

## 输出契约

仅一份 markdown 文件: `{research_md_relpath}`. 完成后用一句话回报 "Stage A done, awaiting user review on {todo_id}".
"""


def build_agent_prompt(todo: TodoSpec, *, research_md_relpath: str) -> str:
    attack_plan_block = "\n".join(f"{i + 1}. {s}" for i, s in enumerate(todo.attack_plan)) or "(看板未列, 自行规划)"
    deliverables_block = "\n".join(f"- {d}" for d in todo.expanded_deliverables()) or "- (看板未列具体路径)"
    worktree_inputs_block = "\n".join(f"- {w}" for w in todo.worktree_inputs) or "- (无显式输入清单, 按需查 lean4/)"
    sub = todo.submission_target()
    return _AGENT_PROMPT.format(
        todo_id=todo.todo_id,
        title=todo.title,
        source=todo.source or "(unknown)",
        type_=todo.type_ or "(unknown)",
        fit_score=todo.fit_score if todo.fit_score is not None else "?",
        topic_score=todo.topic_score if todo.topic_score is not None else "?",
        effort=todo.effort or "?",
        risk=todo.risk or "?",
        untouched=todo.untouched or "(看板未列)",
        statement=todo.statement or "(空)",
        prior=todo.prior or "(看板未列)",
        omega_fit_detail=todo.omega_fit_detail or "(看板未列, 调研者自行评估)",
        attack_plan_block=attack_plan_block,
        deliverables_block=deliverables_block,
        worktree_inputs_block=worktree_inputs_block,
        submission_type=sub["type"],
        submission_venue=sub["venue"],
        submission_format=sub["format"],
        research_md_relpath=research_md_relpath,
    )


# ---------------------------------------------------------------------------
# Planning
# ---------------------------------------------------------------------------


def _branch_name(todo: TodoSpec) -> str:
    slug = todo.slug().replace("_", "-")
    return f"outreach/{slug}"


def plan_dispatch(
    todo_id: str,
    *,
    board_path: Path = BOARD_PATH_DEFAULT,
    repo_root: Path = REPO_ROOT_DEFAULT,
    worktree_root: Path | None = None,
    state_dir: Path | None = None,
) -> DispatchPlan:
    todos = parse_board(board_path)
    if todo_id not in todos:
        raise KeyError(f"{todo_id} not found in {board_path}; available: {sorted(todos)}")
    todo = todos[todo_id]
    slug = todo.slug()
    worktree_root = worktree_root or WORKTREE_ROOT_DEFAULT
    state_dir = state_dir or STATE_DIR_DEFAULT
    branch = _branch_name(todo)
    worktree_path = (worktree_root / slug).resolve()
    target_dir_in_worktree = worktree_path / "tools/community-outreach/targets" / slug
    research_md_path = target_dir_in_worktree / "research.md"
    research_md_relpath = research_md_path.relative_to(worktree_path).as_posix()
    state_json_path = state_dir / f"{slug}.json"
    prompt = build_agent_prompt(todo, research_md_relpath=research_md_relpath)
    return DispatchPlan(
        todo=todo,
        repo_root=repo_root,
        branch=branch,
        worktree_path=worktree_path,
        target_dir_in_worktree=target_dir_in_worktree,
        state_json_path=state_json_path,
        research_md_path=research_md_path,
        agent_prompt=prompt,
        submission_target=todo.submission_target(),
    )


# ---------------------------------------------------------------------------
# Side-effecting actions (gated behind explicit CLI flags)
# ---------------------------------------------------------------------------


def _run(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)


def _git(args: list[str], cwd: Path) -> str:
    res = _run(["git"] + args, cwd=cwd)
    if res.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {res.stderr.strip()}")
    return res.stdout.strip()


def _branch_exists(repo_root: Path, branch: str) -> bool:
    res = _run(["git", "rev-parse", "--verify", "--quiet", branch], cwd=repo_root)
    return res.returncode == 0


def _worktree_exists(repo_root: Path, path: Path) -> bool:
    res = _run(["git", "worktree", "list", "--porcelain"], cwd=repo_root)
    if res.returncode != 0:
        return False
    return str(path) in res.stdout


def create_worktree(plan: DispatchPlan, *, base_branch: str = "outreach-clean") -> Path:
    """Create the git worktree for this dispatch. Idempotent."""
    repo_root = plan.repo_root
    worktree_path = plan.worktree_path
    branch = plan.branch
    worktree_path.parent.mkdir(parents=True, exist_ok=True)
    if _worktree_exists(repo_root, worktree_path):
        return worktree_path
    if _branch_exists(repo_root, branch):
        _git(["worktree", "add", str(worktree_path), branch], cwd=repo_root)
    else:
        _git(["worktree", "add", "-b", branch, str(worktree_path), base_branch], cwd=repo_root)
    return worktree_path


def seed_state_json(plan: DispatchPlan, *, force: bool = False) -> Path:
    """Initialize per-target outreach_state JSON in stage A, round 0."""
    state_path = plan.state_json_path
    state_path.parent.mkdir(parents=True, exist_ok=True)
    if state_path.exists() and not force:
        return state_path
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    state = {
        "schema_version": SCHEMA_VERSION,
        "todo_id": plan.todo.todo_id,
        "title": plan.todo.title,
        "source": plan.todo.source,
        "submission_target": plan.submission_target,
        "branch": plan.branch,
        "worktree_path": str(plan.worktree_path),
        "deliverables_planned": plan.todo.expanded_deliverables(),
        "research_md_path": str(plan.research_md_path),
        "stage": "A",
        "round": 0,
        "scores": {"codex": [], "claude": [], "final": []},
        "findings": [],
        "action_history": [
            {
                "timestamp": now,
                "stage": "A",
                "round": 0,
                "action": "dispatched from RESEARCH_BOARD",
                "detail": f"todo={plan.todo.todo_id} fit={plan.todo.fit_score} topic={plan.todo.topic_score}",
            }
        ],
        "timestamps": {"created_at": now, "updated_at": now, "stage_a_started_at": now},
        "submission_url": "",
        "error": "",
    }
    state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
    return state_path


# ---------------------------------------------------------------------------
# Research-board supervisor
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SupervisorProfile:
    todo_id: str
    slug: str
    commands: tuple[tuple[str, ...], ...]
    value_score: int
    rationale: str


def _target_slug_for_todo(todo: TodoSpec) -> str:
    return TARGET_SLUG_OVERRIDES.get(todo.todo_id, todo.slug())


def _python_cmd(repo_root: Path, *parts: str) -> tuple[str, ...]:
    return (sys.executable, *parts)


def supervisor_profile(todo: TodoSpec, repo_root: Path) -> SupervisorProfile:
    slug = _target_slug_for_todo(todo)
    if todo.todo_id == "T-01":
        return SupervisorProfile(
            todo_id=todo.todo_id,
            slug=slug,
            value_score=6,
            rationale="finite certificate value; live literature reduced broad novelty",
            commands=(
                _python_cmd(
                    repo_root,
                    "tools/community-outreach/targets/erdos_475/p475_valid_ordering.py",
                    "--pmax",
                    "23",
                    "--max-nodes",
                    "100000",
                    "--max-seconds-per-set",
                    "1.0",
                    "--random-trials-per-set",
                    "500000",
                    "--random-p",
                    "29",
                    "--random-sizes",
                    "15-24",
                    "--random-samples",
                    "50",
                    "--seed",
                    "475",
                    "--emit-certificates",
                    "--certificate-path",
                    "tools/community-outreach/targets/erdos_475/p475_certificates_p23.jsonl",
                ),
                _python_cmd(
                    repo_root,
                    "tools/community-outreach/targets/erdos_475/p475_valid_ordering.py",
                    "--verify-certificates",
                    "tools/community-outreach/targets/erdos_475/p475_certificates_p23.jsonl",
                    "--pmax",
                    "23",
                ),
            ),
        )
    if todo.todo_id == "T-02":
        return SupervisorProfile(
            todo_id=todo.todo_id,
            slug=slug,
            value_score=7,
            rationale="current topic; next value is certificate framework, not more naive search",
            commands=(
                _python_cmd(
                    repo_root,
                    "tools/community-outreach/targets/erdos_199/erdos199_min_overlap.py",
                    "--exact-max",
                    "12",
                    "--heuristic-n",
                    "40",
                    "80",
                    "160",
                    "320",
                    "--starts",
                    "64",
                    "--steps",
                    "1800",
                    "--haugland-n",
                    "510",
                    "1020",
                    "2040",
                    "4080",
                    "8160",
                    "--haugland-trials",
                    "250",
                    "--seed",
                    "199",
                ),
            ),
        )
    if todo.todo_id == "T-08":
        return SupervisorProfile(
            todo_id=todo.todo_id,
            slug=slug,
            value_score=8,
            rationale="short solved theorem; strong fit for formalization/backflow",
            commands=(
                _python_cmd(
                    repo_root,
                    "tools/community-outreach/targets/opg_lucas_mod_m/lucas_complete_residue.py",
                    "--limit",
                    "100000",
                ),
            ),
        )
    return SupervisorProfile(
        todo_id=todo.todo_id,
        slug=slug,
        value_score=(todo.fit_score or 0) + (todo.topic_score or 0),
        rationale="generic board target; no safe local experiment profile registered",
        commands=(),
    )


def _load_json(path: Path) -> dict[str, object]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    except json.JSONDecodeError as exc:
        return {"error": f"invalid json: {exc}"}


def _run_supervisor_command(
    cmd: tuple[str, ...],
    *,
    cwd: Path,
    log_dir: Path,
    label: str,
) -> dict[str, object]:
    started = datetime.now(timezone.utc)
    res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    finished = datetime.now(timezone.utc)
    stdout_path = log_dir / f"{label}.stdout.log"
    stderr_path = log_dir / f"{label}.stderr.log"
    stdout_path.write_text(res.stdout, encoding="utf-8")
    stderr_path.write_text(res.stderr, encoding="utf-8")
    return {
        "label": label,
        "cmd": list(cmd),
        "returncode": res.returncode,
        "started_at": started.isoformat(timespec="seconds"),
        "finished_at": finished.isoformat(timespec="seconds"),
        "stdout_log": str(stdout_path),
        "stderr_log": str(stderr_path),
    }


def _analyze_t01(target_dir: Path) -> tuple[str, int, list[str], list[str]]:
    data = _load_json(target_dir / "p475_results.json")
    if not data:
        return "MISSING_RESULTS", 2, ["p475_results.json missing"], ["rerun local finite scan"]
    exhaustive = data.get("exhaustive", [])
    random_rows = data.get("random", [])
    if not isinstance(exhaustive, list) or not isinstance(random_rows, list):
        return "RESULT_SCHEMA_ERROR", 2, ["p475_results.json has unexpected shape"], ["repair result schema"]
    verified_rows = [r for r in exhaustive if isinstance(r, dict) and r.get("status") == "verified"]
    bad_rows = [r for r in exhaustive if isinstance(r, dict) and r.get("status") != "verified"]
    reps = sum(int(r.get("orbit_representatives", 0) or 0) for r in verified_rows if isinstance(r, dict))
    subsets = sum(int(r.get("total_subsets", 0) or 0) for r in verified_rows if isinstance(r, dict))
    random_open = [r for r in random_rows if isinstance(r, dict) and r.get("status") != "valid"]
    cert_path = target_dir / "p475_certificates_p23.jsonl"
    cert_rows = 0
    if cert_path.exists():
        with cert_path.open(encoding="utf-8") as f:
            cert_rows = sum(1 for line in f if line.strip())
    final_draft = target_dir / "submission_draft_final.md"
    findings = [
        f"exhaustive verified rows={len(verified_rows)}, subsets={subsets}, orbit_reps={reps}",
        f"nonverified exhaustive rows={len(bad_rows)}",
        f"p=29 exploratory samples={len(random_rows)}, nonvalid/open={len(random_open)}",
        f"certificate rows={cert_rows}",
        f"final draft present={final_draft.exists()}",
    ]
    if bad_rows:
        return "NEEDS_RERUN", 4, findings, ["increase finite-search budget before drafting"]
    if cert_rows == reps and reps > 0 and final_draft.exists():
        return (
            "DRAFT_READY_CLAUDE_REVIEWED",
            8,
            findings,
            [
                "show final markdown to user for approval before any external posting",
                "after explicit approval, use the selected external channel only",
                "if the user requests edits, rerun Claude review on the revised draft",
            ],
        )
    if cert_rows == reps and reps > 0:
        return (
            "CERTIFICATE_READY",
            7,
            findings,
            [
                "draft finite-certificate outreach note from verified JSONL certificate table",
                "keep claim scoped to p<=23 gap cases plus p=29 exploratory samples",
                "route through Claude review before showing the final external text",
            ],
        )
    return (
        "CERTIFICATE_ENGINE_NEEDED",
        6,
        findings,
        [
            "add full certificate emission for each orbit representative",
            "add independent verifier for orbit coverage and partial-sum distinctness",
            "keep Stage C narrow: finite certificate/formalization note, not broad asymptotic claim",
        ],
    )


def _analyze_t02(target_dir: Path) -> tuple[str, int, list[str], list[str]]:
    data = _load_json(target_dir / "erdos199_results.json")
    if not data:
        return "MISSING_RESULTS", 2, ["erdos199_results.json missing"], ["rerun Stage B overlap script"]
    exact = data.get("exact", [])
    haugland = data.get("haugland51_finite_samples", [])
    if not isinstance(exact, list) or not isinstance(haugland, list):
        return "RESULT_SCHEMA_ERROR", 2, ["erdos199_results.json has unexpected shape"], ["repair result schema"]
    exact_max = max((int(r.get("n", 0) or 0) for r in exact if isinstance(r, dict)), default=0)
    largest_h = max((r for r in haugland if isinstance(r, dict)), key=lambda r: int(r.get("n", 0) or 0), default={})
    h_n = int(largest_h.get("n", 0) or 0)
    h_ratio = float(largest_h.get("ratio", 0.0) or 0.0)
    findings = [
        f"exact finite search complete through n={exact_max}",
        f"largest Haugland finite sample n={h_n}, ratio={h_ratio:.6f}",
        "Omega collision-Hölder route remains trivial at asymptotic ratio 1/4",
    ]
    return (
        "CERTIFICATE_ENGINE_NEEDED",
        7,
        findings,
        [
            "build White-style Fourier/convex dual certificate verifier",
            "separately build public step-function upper-bound verifier",
            "do not pitch AlphaEvolve as current SOTA; use 2026 TTT/SimpleTES frontier language",
        ],
    )


def _analyze_t08(target_dir: Path) -> tuple[str, int, list[str], list[str]]:
    data = _load_json(target_dir / "lucas_complete_residue_summary.json")
    if not data:
        return "MISSING_RESULTS", 2, ["lucas_complete_residue_summary.json missing"], ["rerun Lucas verifier"]
    limit = int(data.get("limit", 0) or 0)
    mismatches = int(data.get("mismatch_count", -1) or 0)
    complete_count = int(data.get("complete_count", 0) or 0)
    findings = [
        f"finite verifier checked m=2..{limit}",
        f"mismatch_count={mismatches}",
        f"complete_count={complete_count}",
    ]
    if mismatches != 0:
        return "INVESTIGATE_MISMATCH", 5, findings, ["inspect mismatches before any draft"]
    return (
        "STAGE_C_READY",
        8 if limit >= 100000 else 7,
        findings,
        [
            "draft Codex submission/backflow note for Avila-Chen reduction",
            "route through Claude review before showing the user",
            "formalization scope should assume/import Burr first, not reprove Burr in outreach",
        ],
    )


def analyze_supervised_target(todo: TodoSpec, profile: SupervisorProfile, repo_root: Path) -> dict[str, object]:
    target_dir = repo_root / "tools/community-outreach/targets" / profile.slug
    research_path = target_dir / "research.md"
    if todo.todo_id == "T-01":
        stage, score, findings, next_actions = _analyze_t01(target_dir)
    elif todo.todo_id == "T-02":
        stage, score, findings, next_actions = _analyze_t02(target_dir)
    elif todo.todo_id == "T-08":
        stage, score, findings, next_actions = _analyze_t08(target_dir)
    else:
        stage = "NO_SUPERVISOR_PROFILE"
        score = profile.value_score
        findings = ["no registered local experiment/analyzer for this TODO"]
        next_actions = ["write a target-specific supervisor profile before running automation"]
    if not research_path.exists():
        stage = "MISSING_RESEARCH"
        score = min(score, 3)
        findings.insert(0, f"missing research.md at {research_path}")
    return {
        "todo_id": todo.todo_id,
        "slug": profile.slug,
        "title": todo.title,
        "source": todo.source,
        "stage": stage,
        "score": score,
        "rationale": profile.rationale,
        "target_dir": str(target_dir),
        "research_md_path": str(research_path),
        "findings": findings,
        "next_actions": next_actions,
        "external_submission_gate": "blocked_pending_user_approval",
    }


def _write_supervisor_state(
    *,
    todo: TodoSpec,
    profile: SupervisorProfile,
    analysis: dict[str, object],
    run_dir: Path,
    command_results: list[dict[str, object]],
    state_dir: Path,
) -> Path:
    """Merge supervisor fields into the per-target state JSON.

    Preserves any dispatch-side fields (branch, worktree_path, deliverables_planned,
    action_history, scores, timestamps, etc.) so the supervisor can run after a
    `seed_state_json` without losing seed metadata.
    """
    state_dir.mkdir(parents=True, exist_ok=True)
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    path = state_dir / f"{profile.slug}.json"
    state: dict[str, object] = _load_json(path) or {}
    # Seed core identity if state was empty (i.e. no prior dispatch).
    state.setdefault("schema_version", SCHEMA_VERSION)
    state.setdefault("todo_id", todo.todo_id)
    state.setdefault("title", todo.title)
    state.setdefault("source", todo.source)
    state.setdefault("slug", profile.slug)
    state.setdefault("submission_target", todo.submission_target())
    # Supervisor-owned fields, namespaced so dispatch fields are not clobbered.
    state["supervisor_schema_version"] = SUPERVISOR_SCHEMA_VERSION
    state["stage"] = analysis["stage"]
    state["score"] = analysis["score"]
    state["supervisor_updated_at"] = now
    state["latest_supervisor_run"] = str(run_dir)
    state["supervisor_command_results"] = command_results
    state["supervisor_analysis"] = analysis
    state["hard_gates"] = {
        "external_submission": "requires explicit user approval after final text preview",
        "lean_execution": "forbidden in community-outreach",
        "lean4_edits": "forbidden in community-outreach",
    }
    # Append to action_history if dispatch seeded one.
    history = state.setdefault("action_history", [])
    if isinstance(history, list):
        history.append(
            {
                "timestamp": now,
                "stage": analysis.get("stage", "?"),
                "round": 0,
                "action": "supervisor analyze",
                "detail": f"score={analysis.get('score')} commands={len(command_results)}",
            }
        )
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return path


def _select_top_todos(todos: dict[str, TodoSpec], n: int) -> list[str]:
    def rank(todo: TodoSpec) -> tuple[int, int, int]:
        risk_penalty = {"low": 0, "low-med": 1, "med": 2, "med-high": 3, "high": 4}.get(todo.risk.strip(), 2)
        return ((todo.fit_score or 0) + (todo.topic_score or 0) - risk_penalty, todo.fit_score or 0, todo.topic_score or 0)

    ordered = sorted(todos.values(), key=rank, reverse=True)
    return [todo.todo_id for todo in ordered[:n]]


def _run_oracle_review(todo: TodoSpec, profile, *, repo_root: Path, oracle_timeout: int) -> dict | None:
    """Stage B-oracle: third-opinion review of research.md by ChatGPT Pro.

    Auto-retry policy (the pipeline self-heals, no human copy-paste):
      - Submit review.
      - If response_valid=False or the response starts with "ERROR":
          1) Wait briefly so the userscript has a chance to /pin-conv-url
             (our patched userscript posts the live /c/<uuid> URL on resume).
          2) Call consultant.retry(task_id=...) → server queues a re-extract
             task that navigates to the existing chat and reads the latest
             assistant message. With patched isSSRGarbage the second pass
             should succeed where the first one false-positived.
      - We retry at most once. Two consecutive failures get recorded.
    """
    try:
        from oracle_consultant import OracleConsultant  # noqa: PLC0415
    except Exception as exc:  # noqa: BLE001
        print(f"[oracle] import failed: {exc}", file=sys.stderr)
        return None
    research_md = repo_root / "tools/community-outreach/targets" / profile.slug / "research.md"
    if not research_md.exists():
        print(f"[oracle] skip {todo.todo_id}: no research.md at {research_md}", file=sys.stderr)
        return {"skipped": "no_research_md", "path": str(research_md)}
    consultant = OracleConsultant()
    if not consultant.is_alive():
        print(f"[oracle] server down at {consultant.server_url}; skipping {todo.todo_id}", file=sys.stderr)
        return {"skipped": "server_down", "server_url": consultant.server_url}
    print(f"[oracle] reviewing {todo.todo_id} (timeout {oracle_timeout}s); "
          f"watch your ChatGPT.com tab with outreach_oracle_macos.user.js ACTIVE")
    review = consultant.review(todo, research_md, timeout=oracle_timeout)
    print(f"[oracle] {todo.todo_id} → verdict={review.verdict} score={review.score} "
          f"chars={review.response_chars} elapsed={review.elapsed_seconds}s "
          f"valid={review.response_valid}")
    needs_retry = (
        not review.response_valid
        or (review.response_chars or 0) < 500
        or (review.error or "").lower().startswith("empty")
    )
    # Auto-retry: re-extract from the same conversation rather than redoing the
    # whole prompt. Cheaper and recovers SSR/timeouts without rerunning ChatGPT
    # thinking from scratch.
    if needs_retry and review.conversation_id:
        print(f"[oracle] retry: response invalid (chars={review.response_chars}, "
              f"valid={review.response_valid}); re-extracting from conv "
              f"{review.conversation_id[:12]}")
        retry_review = consultant.retry(
            task_id=review.task_id,
            conversation_id=review.conversation_id,
            timeout=oracle_timeout,
        )
        if retry_review and retry_review.response_valid:
            print(f"[oracle] retry succeeded: chars={retry_review.response_chars} "
                  f"verdict={retry_review.verdict} score={retry_review.score}")
            # Re-merge into THIS target's state with the recovered review
            try:
                consultant._merge_into_state(slug=profile.slug, review=retry_review)
            except Exception as exc:  # noqa: BLE001
                print(f"[oracle] retry merge failed: {exc}", file=sys.stderr)
            return retry_review.to_dict()
        elif retry_review:
            print(f"[oracle] retry also invalid: chars={retry_review.response_chars} "
                  f"error={retry_review.error[:80]}")
    return review.to_dict()


def _run_oracle_deep(todo: TodoSpec, profile, *, repo_root: Path,
                     state_dir: Path, oracle_timeout: int, max_turns: int,
                     write_latex: bool, codex_driver: bool = False,
                     ship_paper: bool = False) -> dict | None:
    """Stage B-oracle-deep: multi-turn deep-reasoning loop (oracle as primary worker).

    Builds the initial framing prompt from the TODO's research.md (if present)
    plus the board metadata, then drives DEFAULT_DEEPENING_PROMPTS for up to
    `max_turns`. Each turn cumulative — ChatGPT keeps full context.
    """
    try:
        from oracle_consultant import (  # noqa: PLC0415
            DEFAULT_WRITE_PAPER_LATEX_PROMPT,
            OracleConsultant,
            codex_driven_prompt_generator,
            generate_outreach_paper,
            run_paper_pipeline,
        )
    except Exception as exc:  # noqa: BLE001
        print(f"[oracle-deep] import failed: {exc}", file=sys.stderr)
        return None
    research_md = repo_root / "tools/community-outreach/targets" / profile.slug / "research.md"
    consultant = OracleConsultant(state_dir=state_dir)
    if not consultant.is_alive():
        print(f"[oracle-deep] server down at {consultant.server_url}; skipping {todo.todo_id}", file=sys.stderr)
        return {"skipped": "server_down", "server_url": consultant.server_url}
    research_text = ""
    if research_md.exists():
        research_text = research_md.read_text(encoding="utf-8")
    initial = _build_deep_initial_prompt(todo, research_text)
    print(f"[oracle-deep] dispatching {todo.todo_id} max_turns={max_turns} "
          f"per-turn-timeout={oracle_timeout}s; this can take up to "
          f"{max_turns} × {oracle_timeout}s = {max_turns * oracle_timeout // 60}min "
          f"write_latex={write_latex} codex_driver={codex_driver}")
    run = consultant.deep_reasoning(
        todo, initial,
        max_turns=max_turns,
        prompt_generator=codex_driven_prompt_generator if codex_driver else None,
        per_turn_timeout=oracle_timeout,
        terminal_prompt=DEFAULT_WRITE_PAPER_LATEX_PROMPT if write_latex else None,
        slug=profile.slug,
    )
    print(f"[oracle-deep] {todo.todo_id} → verdict={run['final_verdict']} "
          f"turns={len(run['turns'])} elapsed={run['total_elapsed_seconds']}s "
          f"conv={run.get('conversation_id','')[:12]}")
    if run.get("latex_path"):
        print(f"[oracle-deep] LaTeX saved: {run['latex_path']}")
    elif run.get("terminal_latex_error"):
        print(f"[oracle-deep] LaTeX not saved: {run['terminal_latex_error']}", file=sys.stderr)
    if write_latex and ship_paper:
        latex_path = run.get("latex_path") or ""
        if not latex_path:
            print("[ship-paper] skipped: no LaTeX path from oracle deep run", file=sys.stderr)
        else:
            try:
                polished = generate_outreach_paper(Path(latex_path))
                paper_result = run_paper_pipeline(
                    polished.parent,
                    log_dir=repo_root / "tools/community-outreach/logs/ship_paper",
                )
                run["paper_pipeline"] = paper_result
                _persist_ship_paper_result(
                    state_dir=state_dir,
                    slug=profile.slug,
                    result=paper_result,
                )
                if paper_result.get("pdf_path") and paper_result.get("exit_code") == 0:
                    _append_outreach_log_transition(
                        repo_root=repo_root,
                        slug=profile.slug,
                        result=paper_result,
                    )
                print(f"[ship-paper] pipeline rc={paper_result['exit_code']} "
                      f"pdf={paper_result.get('pdf_path','') or '(none)'}")
            except Exception as exc:  # noqa: BLE001
                paper_result = {
                    "paper_dir": str(Path(latex_path).parent),
                    "pdf_path": "",
                    "pipeline_log": "",
                    "stages_completed": [],
                    "exit_code": -1,
                    "error": str(exc),
                }
                run["paper_pipeline"] = paper_result
                _persist_ship_paper_result(
                    state_dir=state_dir,
                    slug=profile.slug,
                    result=paper_result,
                )
                print(f"[ship-paper] failed: {exc}", file=sys.stderr)
    return run


def _persist_ship_paper_result(*, state_dir: Path, slug: str, result: dict) -> None:
    state_dir.mkdir(parents=True, exist_ok=True)
    path = state_dir / f"{slug}.json"
    try:
        state = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    except json.JSONDecodeError:
        state = {}
    state["outreach_paper_pdf"] = result.get("pdf_path", "")
    state["paper_pipeline_log"] = result.get("pipeline_log", "")
    state["paper_pipeline_exit_code"] = result.get("exit_code", -1)
    state["paper_pipeline_error"] = result.get("error", "")
    state["paper_pipeline_stages_completed"] = result.get("stages_completed", [])
    history = state.setdefault("action_history", [])
    if isinstance(history, list):
        history.append({
            "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "stage": "ship-paper",
            "round": 0,
            "action": "oracle paper pipeline",
            "detail": (f"rc={result.get('exit_code', -1)} "
                       f"pdf={result.get('pdf_path', '')} "
                       f"log={result.get('pipeline_log', '')}"),
        })
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8")


def _append_outreach_log_transition(*, repo_root: Path, slug: str, result: dict) -> None:
    pdf_path = result.get("pdf_path", "") or ""
    pdf_size = 0
    if pdf_path:
        try:
            pdf_size = Path(pdf_path).stat().st_size
        except OSError:
            pdf_size = 0
    timestamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    entry = (f"- {timestamp} {slug}: paper_drafted -> paper_pdf_ready "
             f"(pdf={pdf_path}, size={pdf_size}B)")
    log_path = repo_root / "tools/community-outreach/OUTREACH_LOG.md"
    if log_path.exists():
        text = log_path.read_text(encoding="utf-8")
    else:
        text = "# Automath Outreach Log\n"
    if not text.strip():
        text = "# Automath Outreach Log\n"
    if "## Status Transitions" in text:
        text = text.rstrip() + "\n" + entry + "\n"
    else:
        text = text.rstrip() + "\n\n## Status Transitions\n\n" + entry + "\n"
    log_path.write_text(text, encoding="utf-8")


def _build_deep_initial_prompt(todo: TodoSpec, research_text: str) -> str:
    sub = todo.submission_target()
    parts = [
        "You are the primary mathematical worker on this Omega Project outreach target.",
        "We will iterate over many turns; your job is to push for genuine progress, not summary.",
        "Each turn you'll get a follow-up that asks you to dig one level deeper.",
        "Stop only when you reach a precise BREAKTHROUGH (proved, calculated, constructed)",
        "or you hit a clearly characterized obstacle you call STUCK with the next-step bypass listed.",
        "",
        f"## Target",
        f"- TODO id: {todo.todo_id}",
        f"- Title: {todo.title}",
        f"- Source: {todo.source}",
        f"- Status (per board): {todo.status}",
        f"- Untouched evidence: {todo.untouched}",
        f"- Submission target (Stage E): {sub['type']} → {sub['venue']}",
        "",
        "## Math problem statement",
        todo.statement or "(see source URL above)",
        "",
        "## What is already known (prior)",
        todo.prior or "(unknown to the board; please survey what you know)",
        "",
        "## Omega library tooling available",
        todo.omega_fit_detail or "(not specified; please ask if you need a specific Lean lemma)",
        "",
        "## Attack plan (preliminary, refine as you go)",
        "\n".join(f"- {step}" for step in (todo.attack_plan or [])) or "- (open to your suggestion)",
        "",
    ]
    if research_text:
        parts += [
            "## research.md drafted by Codex (verbose; treat as background, not gospel)",
            research_text[:30000],
            "",
        ]
    parts += [
        "## Your first turn",
        "Give your initial concrete attack on this problem. Aim for:",
        "  1. A precise restatement of the most reachable sub-goal (one line).",
        "  2. The mathematical machinery you'd use (specific lemmas / techniques).",
        "  3. The first three concrete calculations or constructions you'd perform.",
        "  4. The expected outcome and how you'd verify it.",
        "Be specific. Show numbers / formulas / explicit constructions.",
        "Do not summarize the problem back to me — go forward.",
    ]
    return "\n".join(parts)


def supervise_board(
    *,
    board_path: Path,
    repo_root: Path,
    todo_ids: list[str],
    top: int,
    run: bool,
    state_dir: Path,
    logs_dir: Path,
    oracle: bool = False,
    oracle_timeout: int = 7200,
    oracle_deep: bool = False,
    oracle_max_turns: int = 10,
    write_latex: bool = False,
    codex_driver: bool = False,
    ship_paper: bool = False,
) -> int:
    todos = parse_board(board_path)
    if not todos:
        print(f"No TODOs parsed from {board_path}", file=sys.stderr)
        return 1
    ids = list(todo_ids)
    if not ids:
        ids = _select_top_todos(todos, top or 3)
    missing = [tid for tid in ids if tid not in todos]
    if missing:
        print(f"Missing TODO ids: {', '.join(missing)}", file=sys.stderr)
        return 1

    run_stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = logs_dir / "research_board" / run_stamp
    run_dir.mkdir(parents=True, exist_ok=True)

    summaries: list[dict[str, object]] = []
    any_failure = False
    for tid in ids:
        todo = todos[tid]
        profile = supervisor_profile(todo, repo_root)
        target_log_dir = run_dir / profile.slug
        target_log_dir.mkdir(parents=True, exist_ok=True)
        command_results: list[dict[str, object]] = []
        if run:
            for index, cmd in enumerate(profile.commands, start=1):
                label = f"{profile.slug}_cmd{index}"
                result = _run_supervisor_command(cmd, cwd=repo_root, log_dir=target_log_dir, label=label)
                command_results.append(result)
                if result["returncode"] != 0:
                    any_failure = True
                    break
        analysis = analyze_supervised_target(todo, profile, repo_root)
        if command_results and any(r.get("returncode") != 0 for r in command_results):
            analysis["stage"] = "COMMAND_FAILED"
            analysis["score"] = min(int(analysis.get("score", 0) or 0), 2)
            analysis.setdefault("findings", [])
            assert isinstance(analysis["findings"], list)
            analysis["findings"].insert(0, "one or more supervised commands failed; inspect stderr logs")
        state_path = _write_supervisor_state(
            todo=todo,
            profile=profile,
            analysis=analysis,
            run_dir=run_dir,
            command_results=command_results,
            state_dir=state_dir,
        )
        analysis["state_json_path"] = str(state_path)
        analysis["commands_run"] = len(command_results)

        # Stage B-oracle (third-opinion). Runs after the supervisor has
        # already written its analysis to state JSON, so the oracle merge sees
        # those fields and only adds oracle_reviews / latest_oracle_* on top.
        if oracle:
            oracle_summary = _run_oracle_review(
                todo, profile, repo_root=repo_root, oracle_timeout=oracle_timeout,
            )
            if oracle_summary is not None:
                analysis["oracle"] = oracle_summary

        # Stage B-oracle-deep: oracle as primary worker, multi-turn iteration.
        if oracle_deep:
            deep_run = _run_oracle_deep(
                todo, profile, repo_root=repo_root,
                state_dir=state_dir,
                oracle_timeout=oracle_timeout, max_turns=oracle_max_turns,
                write_latex=write_latex,
                codex_driver=codex_driver,
                ship_paper=ship_paper,
            )
            if deep_run is not None:
                analysis["oracle_deep"] = deep_run

        summaries.append(analysis)

    summary_path = run_dir / "summary.json"
    summary_path.write_text(json.dumps(summaries, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Supervisor run: {run_dir}")
    print(f"Summary JSON: {summary_path}")
    for item in summaries:
        print(
            f"{item['todo_id']} {item['slug']}: stage={item['stage']} "
            f"score={item['score']} commands={item['commands_run']}"
        )
        for finding in item.get("findings", [])[:3]:
            print(f"  - {finding}")
        next_actions = item.get("next_actions", [])
        if next_actions:
            print(f"  next: {next_actions[0]}")
        oracle_summary = item.get("oracle")
        if isinstance(oracle_summary, dict):
            if "skipped" in oracle_summary:
                print(f"  oracle: skipped ({oracle_summary['skipped']})")
            else:
                print(f"  oracle: verdict={oracle_summary.get('verdict','')} "
                      f"score={oracle_summary.get('score','')} "
                      f"conv={(oracle_summary.get('conversation_id','') or '')[:12]} "
                      f"elapsed={oracle_summary.get('elapsed_seconds',0)}s")
                tr = oracle_summary.get("top_recommendation", "")
                if tr:
                    print(f"    top-rec: {tr[:80]}")
    return 1 if any_failure else 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _summary_row(t: TodoSpec) -> str:
    fit = f"{t.fit_score}/10" if t.fit_score is not None else "?/10"
    topic = f"{t.topic_score}/10" if t.topic_score is not None else "?/10"
    return f"{t.todo_id:>5}  fit={fit:5}  topic={topic:5}  effort={t.effort:<10}  risk={t.risk:<8}  {t.title}"


def _list_todos(board_path: Path) -> int:
    todos = parse_board(board_path)
    if not todos:
        print(f"No TODOs parsed from {board_path}", file=sys.stderr)
        return 1
    print(f"# {len(todos)} TODOs in {board_path}\n")
    for tid in sorted(todos, key=lambda x: int(x.split("-")[1])):
        print(_summary_row(todos[tid]))
    return 0


def _print_plan(plan: DispatchPlan, as_json: bool) -> None:
    if as_json:
        print(json.dumps(plan.to_serializable(), ensure_ascii=False, indent=2))
        return
    t = plan.todo
    print(f"# Dispatch plan for {t.todo_id} · {t.title}\n")
    print(f"slug:           {t.slug()}")
    print(f"branch:         {plan.branch}")
    print(f"worktree path:  {plan.worktree_path}")
    print(f"research.md:    {plan.research_md_path}")
    print(f"state JSON:     {plan.state_json_path}")
    print(f"submission:     {plan.submission_target['type']} → {plan.submission_target['venue']}")
    print(f"fit / topic:    {t.fit_score}/10  /  {t.topic_score}/10")
    print(f"effort / risk:  {t.effort}  /  {t.risk}")
    print(f"\n--- agent prompt ({len(plan.agent_prompt)} chars) ---")
    print(plan.agent_prompt)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("todo_id", nargs="?", help="TODO ID like T-18")
    parser.add_argument("--list", action="store_true", help="List all TODOs and exit")
    parser.add_argument("--json", action="store_true", help="Emit dispatch plan as JSON")
    parser.add_argument("--create", action="store_true", help="Create git worktree (side effect)")
    parser.add_argument("--seed-state", action="store_true", help="Seed outreach_state JSON (side effect)")
    parser.add_argument("--force-state", action="store_true", help="Overwrite existing state JSON")
    parser.add_argument("--base-branch", default="outreach-clean", help="Base branch for new worktree")
    parser.add_argument("--board", default=str(BOARD_PATH_DEFAULT), help="Path to RESEARCH_BOARD.md")
    parser.add_argument("--repo-root", default=str(REPO_ROOT_DEFAULT), help="Repo root")
    parser.add_argument("--worktree-root", default=None, help="Where to put worktrees")
    parser.add_argument("--state-dir", default=None, help="Where to put state JSON")
    parser.add_argument("--supervise", action="store_true", help="Run RESEARCH_BOARD supervisor")
    parser.add_argument("--supervise-id", action="append", default=[], help="TODO ID to supervise; repeatable")
    parser.add_argument("--top", type=int, default=3, help="With --supervise and no --supervise-id, choose top N TODOs")
    parser.add_argument("--run", action="store_true", help="With --supervise, rerun registered safe local experiments")
    parser.add_argument("--logs-dir", default=str(LOGS_DIR_DEFAULT), help="Where supervisor logs are written")
    parser.add_argument("--oracle", action="store_true",
                        help="With --supervise, send research.md to outreach oracle as a single-shot "
                             "third-opinion review (Stage B). Auto-retries on extraction failure.")
    parser.add_argument("--oracle-discover", action="store_true",
                        help="Round 1: send paper digest + RESEARCH_BOARD candidates to oracle, "
                             "ask for capability-aware ranking (which TODOs are real, doable, valuable). "
                             "Single-shot. No --supervise required.")
    parser.add_argument("--oracle-discover-then-deep", action="store_true",
                        help="Round 1 + Round 2 chained: discover, then automatically dispatch "
                             "deep-reasoning on the TOP-1 target oracle picks. Caution: total runtime "
                             "= discover poll + (max_turns × per-turn timeout).")
    parser.add_argument("--oracle-deep", action="store_true",
                        help="Round 2 only: with --supervise, run the multi-turn deep-reasoning loop "
                             "on the target. Oracle becomes the primary worker.")
    parser.add_argument("--write-latex", action="store_true",
                        help="With --oracle-deep or --oracle-discover-then-deep, send the terminal "
                             "WRITE_PAPER_LATEX turn after BREAKTHROUGH and save theory/2026_outreach_<slug>/main.tex.")
    parser.add_argument("--codex-driver", action="store_true",
                        help="Use codex to generate each follow-up prompt instead of templated rotation. "
                             "Each turn ~30-60s extra latency.")
    parser.add_argument("--ship-paper", action="store_true",
                        help="With --oracle-deep and --write-latex, polish the saved LaTeX and run the "
                             "paper pipeline to the first user gate.")
    parser.add_argument("--oracle-max-turns", type=int, default=10,
                        help="With --oracle-deep, max rounds of deepening (default 10)")
    parser.add_argument("--oracle-timeout", type=int, default=7200,
                        help="Per-turn oracle timeout in seconds (default 7200 = 2h)")
    parser.add_argument("--arxiv-watch", action="store_true",
                        help="Round 0 lit-staleness booster: scan recent arXiv math papers "
                             "against active board targets via NyxID arxiv-api proxy.")
    parser.add_argument("--arxiv-since", default="7d",
                        help="With --arxiv-watch, time window (default 7d).")
    parser.add_argument("--draft-tweet", action="store_true",
                        help="Round 6.5: generate an X (Twitter) thread draft from pipeline "
                             "state for <todo_id>. Saves to drafts/<id>_tweet.txt for review. "
                             "Never auto-posts (use x_broadcast.py post --confirm-post).")
    args = parser.parse_args(list(argv) if argv is not None else None)

    board_path = Path(args.board)
    repo_root = Path(args.repo_root)
    state_dir = Path(args.state_dir) if args.state_dir else STATE_DIR_DEFAULT

    if args.arxiv_watch:
        import arxiv_watch  # noqa: PLC0415
        return arxiv_watch.main(["--since", args.arxiv_since, "--board", str(board_path)])

    if args.draft_tweet:
        if not args.todo_id:
            print("--draft-tweet requires a TODO id (e.g. T-21)", file=sys.stderr)
            return 1
        import x_broadcast  # noqa: PLC0415
        return x_broadcast.main(["draft", args.todo_id])
    if args.oracle_discover or args.oracle_discover_then_deep:
        from oracle_consultant import OracleConsultant, discover_targets  # noqa: PLC0415
        todos = parse_board(board_path)
        consultant = OracleConsultant()
        if not consultant.is_alive():
            print(f"[discover] oracle server down at {consultant.server_url}; "
                  "start outreach_oracle_server.py", file=sys.stderr)
            return 1
        print(f"[discover] dispatching capability-aware scope check on "
              f"{len(todos)} board TODOs (timeout {args.oracle_timeout}s)")
        report = discover_targets(consultant, todos, timeout=args.oracle_timeout)
        print(f"[discover] response: {report.response_chars} chars, "
              f"valid={report.response_valid}, conv={report.conversation_id[:12]}")
        if not report.response_valid:
            print(f"[discover] error: {report.error}", file=sys.stderr)
            return 2
        print()
        print(f"=== Discarded ({len(report.discarded)}) ===")
        for d in report.discarded:
            print(f"  {d['todo_id']}: {d['reason'][:120]}")
        print()
        print(f"=== Ranked survivors (top 8) ===")
        for r in report.ranked[:8]:
            print(f"  {r['todo_id']} {r['title'][:50]}: {r['reason'][:140]}")
        print()
        print(f"=== TOP-3 picks ===")
        for p in report.top_picks:
            print(f"  {p['todo_id']}: {p['rationale'][:200]}")
        print()
        if report.top1_subgoal:
            print(f"=== TOP-1 sub-goal ===")
            for k in ("target", "sub_goal", "omega_fit", "publication", "days"):
                if k in report.top1_subgoal:
                    print(f"  {k}: {report.top1_subgoal[k]}")
        print()
        print(f"Full discovery report: tools/community-outreach/discovery/discover_*.json")
        if args.oracle_discover_then_deep and report.top1_subgoal.get("target"):
            top_target = report.top1_subgoal["target"].strip()
            # extract T-NN from target field (might be "T-21" or "T-21 Goel ...")
            m = re.match(r"(T-\d+)", top_target)
            if not m:
                print(f"[discover] could not parse target id from '{top_target}'; aborting deep round",
                      file=sys.stderr)
                return 0
            tid = m.group(1)
            print(f"\n[discover→deep] auto-dispatching deep reasoning on {tid}")
            return supervise_board(
                board_path=board_path, repo_root=repo_root,
                todo_ids=[tid], top=1, run=False,
                state_dir=state_dir, logs_dir=Path(args.logs_dir),
                oracle=False,
                oracle_timeout=args.oracle_timeout,
                oracle_deep=True,
                oracle_max_turns=args.oracle_max_turns,
                write_latex=args.write_latex,
                codex_driver=args.codex_driver,
                ship_paper=args.ship_paper,
            )
        return 0

    if args.supervise:
        ids = list(args.supervise_id)
        if args.todo_id:
            ids.append(args.todo_id)
        return supervise_board(
            board_path=board_path,
            repo_root=repo_root,
            todo_ids=ids,
            top=args.top,
            run=args.run,
            state_dir=state_dir,
            logs_dir=Path(args.logs_dir),
            oracle=args.oracle,
            oracle_timeout=args.oracle_timeout,
            oracle_deep=args.oracle_deep,
            oracle_max_turns=args.oracle_max_turns,
            write_latex=args.write_latex,
            codex_driver=args.codex_driver,
            ship_paper=args.ship_paper,
        )

    if args.list or not args.todo_id:
        return _list_todos(board_path)

    plan = plan_dispatch(
        args.todo_id,
        board_path=board_path,
        repo_root=repo_root,
        worktree_root=Path(args.worktree_root) if args.worktree_root else None,
        state_dir=state_dir,
    )
    if args.create:
        path = create_worktree(plan, base_branch=args.base_branch)
        print(f"worktree ready: {path}", file=sys.stderr)
    if args.seed_state:
        path = seed_state_json(plan, force=args.force_state)
        print(f"state JSON: {path}", file=sys.stderr)
    _print_plan(plan, as_json=args.json)
    return 0


if __name__ == "__main__":
    sys.exit(main())
