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
import os
import re
import signal
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

# Board parsing primitives now live in a zero-dependency module so that
# arxiv_watch / lit_staleness / oracle_consultant / resume_deep do not
# fail to start when dispatch_worktree.py has any import-time bug.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from outreach_board_parser import (  # noqa: E402
    BOARD_PATH_DEFAULT,
    TARGET_SLUG_OVERRIDES,
    TodoSpec,
    parse_board,
)
from outreach_profile import load_profile  # noqa: E402
from outreach_science_gate import science_contract_block  # noqa: E402

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
STATE_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/outreach_state"
TARGETS_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/targets"
LOGS_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/logs"
WORKTREE_ROOT_DEFAULT = REPO_ROOT_DEFAULT.parent / "_outreach_worktrees"
LOCAL_REPAIR_SCRIPT_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/outreach_local_repair.py"
SCHEMA_VERSION = "community-outreach-state-v3-research-board"
SUPERVISOR_SCHEMA_VERSION = "community-outreach-supervisor-v1"
PRE_ORACLE_WORKUP_REUSE_SECONDS = int(os.environ.get("OUTREACH_PRE_ORACLE_WORKUP_REUSE_SECONDS", "900") or "900")
PRE_ORACLE_WORKUP_GATE_CHARS = int(os.environ.get("OUTREACH_PRE_ORACLE_WORKUP_GATE_CHARS", "60000") or "60000")

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

## 科学完成契约 (必须围绕这个写 research.md)

{science_contract_block}

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
   - “Science Contract Status”: 明确当前离 terminal artifact 还差什么证据；下一步必须降低哪个 progress_metric
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
    profile, _ = load_profile(todo.slug())
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
        science_contract_block=science_contract_block(profile),
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


def _terminate_process_group(proc: subprocess.Popen, *, grace_seconds: float = 5.0) -> None:
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except (ProcessLookupError, OSError):
        return
    try:
        proc.wait(timeout=grace_seconds)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, OSError):
        pass


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


def _run_arxiv_watch_for_todo(
    todo: TodoSpec,
    *,
    target_log_dir: Path,
    since: str = "14d",
    max_results: int = 400,
) -> dict | None:
    """Stage 0: scan recent arXiv for papers overlapping this TODO. Best-effort.

    Returns a dict with `hits` list (possibly empty) and `since`, or None on
    catastrophic failure (we never let arxiv-watch failure abort the supervise
    flow — the rest of the pipeline runs fine without it).
    """
    try:
        import arxiv_watch  # noqa: PLC0415
    except Exception as exc:  # noqa: BLE001
        print(f"[arxiv_watch] import failed for {todo.todo_id}: {exc}", file=sys.stderr)
        return None
    out_path = target_log_dir / "arxiv_watch.json"
    argv = [
        "--since", since,
        "--max-results", str(max_results),
        "--only", todo.todo_id,
        "--json", str(out_path),
    ]
    try:
        rc = arxiv_watch.main(argv)
    except SystemExit as exc:
        rc = int(exc.code or 0)
    except Exception as exc:  # noqa: BLE001
        print(f"[arxiv_watch] {todo.todo_id} crashed: {exc}", file=sys.stderr)
        return None
    if rc != 0 or not out_path.exists():
        return None
    try:
        report = json.loads(out_path.read_text())
    except Exception as exc:  # noqa: BLE001
        print(f"[arxiv_watch] {todo.todo_id} JSON parse failed: {exc}", file=sys.stderr)
        return None
    hits = report.get("hits", []) or []
    if hits:
        # Print compact warning so supervisors see freshness signal at a glance.
        print(f"[arxiv_watch] {todo.todo_id}: {len(hits)} recent paper(s) overlap "
              f"(since {since}); see {out_path}", file=sys.stderr)
        for h in hits[:3]:
            paper = h.get("paper", {})
            print(f"    score={h.get('overlap_score')} "
                  f"matched={','.join(h.get('matched_keywords', []))} | "
                  f"{paper.get('title','')[:80]} ({paper.get('published','')})",
                  file=sys.stderr)
    return {
        "since": report.get("since"),
        "papers_scanned": report.get("papers_scanned"),
        "hits": hits,
        "report_path": str(out_path),
    }


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
                     ship_paper: bool = False,
                     arxiv_hits: list[dict] | None = None,
                     resume_conversation_id: str = "") -> dict | None:
    """Stage B-oracle-deep: one bounded deep-reasoning batch.

    Builds the initial framing prompt from the TODO's research.md (if present)
    plus the board metadata, then drives prompts for up to `max_turns`.
    This is an engineering watchdog for one batch, not a scientific stop
    condition. outreach_research_loop re-runs science/impact gates after the
    batch and schedules another batch if the target still needs evidence.
    """
    try:
        from oracle_consultant import (  # noqa: PLC0415
            DEFAULT_WRITE_PAPER_LATEX_PROMPT,
            OracleConsultant,
            codex_driven_prompt_generator,
            generate_outreach_paper,
            oracle_bridge_readiness,
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
    ready, ready_reason, ready_status = oracle_bridge_readiness(consultant.server_url)
    if not ready:
        print(
            f"[oracle-deep] bridge not ready for {todo.todo_id}: {ready_reason}",
            file=sys.stderr,
        )
        return {
            "skipped": "bridge_not_ready",
            "reason": ready_reason,
            "server_url": consultant.server_url,
            "required_script_version": ready_status.get("required_script_version", ""),
            "active_poll_agents": ready_status.get("active_poll_agents", []),
            "compatible_active_poll_agents": ready_status.get("compatible_active_poll_agents", []),
        }
    workup_ok, workup_reason, workup_log = _run_pre_oracle_codex_workup(
        todo.todo_id,
        profile.slug,
        timeout=oracle_timeout,
    )
    if not workup_ok:
        print(
            f"[oracle-deep] pre-oracle Codex workup failed for {todo.todo_id}: "
            f"{workup_reason} ({workup_log})",
            file=sys.stderr,
        )
        return {
            "skipped": "pre_oracle_codex_workup_required",
            "reason": workup_reason,
            "local_repair_log": workup_log,
            "target_slug": profile.slug,
            "required_artifacts": [
                f"tools/community-outreach/targets/{profile.slug}/codex_workup.md",
                f"tools/community-outreach/targets/{profile.slug}/next_oracle_question.md",
                f"tools/community-outreach/targets/{profile.slug}/local_repair_report.md",
            ],
        }
    print(f"[oracle-deep] pre-oracle Codex workup refreshed for {todo.todo_id}: {workup_log}")
    research_text = ""
    if research_md.exists():
        research_text = research_md.read_text(encoding="utf-8")
    resume_conv = resume_conversation_id or _resume_conversation_id(profile.slug, state_dir=state_dir)
    if resume_conv:
        initial = _build_deep_resume_prompt(todo, resume_conversation_id=resume_conv)
    else:
        initial = _build_deep_initial_prompt(
            todo,
            research_text,
            arxiv_hits=arxiv_hits,
            resume_conversation_id="",
        )
    print(f"[oracle-deep] dispatching {todo.todo_id} max_turns={max_turns} "
          f"per-turn-timeout={oracle_timeout}s; this can take up to "
          f"{max_turns} × {oracle_timeout}s = {max_turns * oracle_timeout // 60}min "
          f"write_latex={write_latex} codex_driver={codex_driver} "
          f"resume_conv={resume_conv[:12] if resume_conv else '-'}")
    run = consultant.deep_reasoning(
        todo, initial,
        max_turns=max_turns,
        prompt_generator=codex_driven_prompt_generator if codex_driver else None,
        per_turn_timeout=oracle_timeout,
        terminal_prompt=DEFAULT_WRITE_PAPER_LATEX_PROMPT if write_latex else None,
        resume_conversation_id=resume_conv,
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


def _latest_oracle_deep_response(run: dict) -> tuple[str, str]:
    """Return (text, path) for the latest nonempty oracle deep response."""
    for turn in reversed(run.get("turns") or []):
        if not isinstance(turn, dict):
            continue
        path = str(turn.get("response") or "").strip()
        if not path:
            continue
        try:
            p = Path(path)
            if p.exists() and p.is_file():
                text = p.read_text(encoding="utf-8", errors="replace").strip()
                if text:
                    return text, str(p)
        except OSError:
            continue
    return "", ""


def _materialize_oracle_deep_research_md(
    todo: TodoSpec,
    profile: SupervisorProfile,
    run: dict,
    *,
    repo_root: Path,
) -> str:
    """Persist the latest oracle deep-reasoning content as target research.md.

    The research loop consumes `targets/<slug>/research.md` as the handoff
    artifact. Without this bridge, `--oracle-deep` may make real mathematical
    progress in logs/state while the next cycle still sees a missing terminal
    artifact and repeats a no-op local supervisor pass.
    """
    text, response_path = _latest_oracle_deep_response(run)
    if not text:
        return ""
    try:
        from oracle_consultant import _materialize_file_blocks  # noqa: PLC0415
        artifacts = _materialize_file_blocks(text)
    except Exception:
        artifacts = []
    target_research_rel = f"tools/community-outreach/targets/{profile.slug}/research.md"
    if target_research_rel in set(artifacts):
        return str(repo_root / target_research_rel)
    target_dir = repo_root / "tools/community-outreach/targets" / profile.slug
    target_dir.mkdir(parents=True, exist_ok=True)
    research_md = target_dir / "research.md"
    completed = run.get("run_completed_at") or datetime.now(timezone.utc).isoformat(timespec="seconds")
    turns = run.get("turns") or []
    turn_lines = []
    for turn in turns:
        if not isinstance(turn, dict):
            continue
        turn_lines.append(
            "- turn={turn} chars={chars} evaluator={evalv} source={source} response={resp}".format(
                turn=turn.get("turn", "?"),
                chars=turn.get("response_chars", 0),
                evalv=turn.get("evaluator_verdict", "") or "-",
                source=turn.get("prompt_source", "") or "-",
                resp=turn.get("response", "") or "-",
            )
        )
    body = "\n".join([
        f"# Oracle Deep Research Artifact — {todo.todo_id} ({profile.slug})",
        "",
        f"Generated: {completed}",
        f"Final verdict: `{run.get('final_verdict', '')}`",
        f"Conversation: `{run.get('conversation_id', '')}`",
        f"ChatGPT URL: {run.get('chatgpt_url', '') or '(not captured)'}",
        f"Latest response log: `{response_path}`",
        "",
        "## Science Contract",
        "",
        science_contract_block(load_profile(todo.slug())[0]),
        "",
        "## Turn Index",
        "",
        "\n".join(turn_lines) or "(no turns recorded)",
        "",
        "## Latest Oracle Research Text",
        "",
        text,
        "",
    ])
    research_md.write_text(body, encoding="utf-8")
    return str(research_md)


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


def _read_research_loop_state(slug: str) -> dict:
    path = STATE_DIR_DEFAULT / f"{slug}.research_loop.json"
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _resume_conversation_id(slug: str, *, state_dir: Path) -> str:
    """Return the latest reusable ChatGPT conversation for this target.

    Browser/network failures should resume the same Project chat instead of
    starting a fresh session and losing the mathematical context. We only resume
    when the last run is non-terminal; WRITEBACK/BREAKTHROUGH flows are handled
    by science/impact gates.
    """
    path = state_dir / f"{slug}.json"
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ""
    latest_status = str(state.get("latest_oracle_deep_verdict") or "").upper()
    if latest_status in {"BREAKTHROUGH"}:
        return ""
    conv = str(state.get("latest_oracle_deep_conversation_id") or "").strip()
    if conv:
        return conv
    runs = state.get("oracle_deep_runs") or []
    if isinstance(runs, list):
        for run in reversed(runs):
            if not isinstance(run, dict):
                continue
            verdict = str(run.get("final_verdict") or "").upper()
            if verdict == "BREAKTHROUGH":
                return ""
            conv = str(run.get("conversation_id") or "").strip()
            if conv:
                return conv
    return ""


def _compact_science_contract_block(profile) -> str:
    """Small Oracle-facing contract.

    Full taste obligations remain enforced by the deterministic local gate.
    Oracle needs the target, verifier, progress metric, and stop/writeback
    criteria, not every audit-field expansion on every turn.
    """
    contract = getattr(profile, "science_contract", None) if profile is not None else None
    if contract is None:
        return "(missing science_contract; ask for target profile repair before claiming completion)"
    fields = [
        ("Contribution type", getattr(contract, "contribution_type", "")),
        ("Target lane", getattr(contract, "target_lane", "")),
        ("Terminal artifact", getattr(contract, "terminal_artifact", "")),
        ("Verifier", getattr(contract, "verifier", "")),
        ("Progress metric", getattr(contract, "progress_metric", "")),
    ]
    lines = [f"{k}: {v or '(unspecified)'}" for k, v in fields]
    evidence = list(getattr(contract, "evidence_required", []) or [])
    writeback = list(getattr(contract, "writeback_when", []) or [])
    close = list(getattr(contract, "close_when", []) or [])
    if evidence:
        lines.append("Evidence required:")
        lines.extend(f"- {x}" for x in evidence[:6])
    if writeback:
        lines.append("Write back only when:")
        lines.extend(f"- {x}" for x in writeback[:4])
    if close:
        lines.append("Close or re-scope when:")
        lines.extend(f"- {x}" for x in close[:4])
    lines.append(f"No-progress patience turns: {getattr(contract, 'no_progress_patience_turns', 2)}")
    return "\n".join(lines)


def _read_target_context_file(slug: str, name: str, *, max_chars: int) -> str:
    path = TARGETS_DIR_DEFAULT / slug / name
    try:
        text = path.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        return ""
    if len(text) <= max_chars:
        return text
    return text[: max_chars // 2] + "\n\n...[middle truncated]...\n\n" + text[-max_chars // 2 :]


def _extract_markdown_section(text: str, heading: str, *, max_chars: int) -> str:
    """Extract a single markdown heading body from a Codex workup."""
    if not text:
        return ""
    pattern = re.compile(
        r"(?ims)^##\s+"
        + re.escape(heading).replace(r"\ ", r"\s+")
        + r"\s*$"
        + r"(.*?)"
        + r"(?=^##\s+|\Z)"
    )
    match = pattern.search(text)
    if not match:
        return ""
    body = match.group(1).strip()
    if len(body) <= max_chars:
        return body
    return body[: max_chars // 2] + "\n\n...[middle truncated]...\n\n" + body[-max_chars // 2 :]


def _extract_workup_section(text: str, heading: str) -> str:
    return _extract_markdown_section(text, heading, max_chars=20000)


def _codex_workup_has_local_trace(text: str) -> bool:
    """Return true only when the workup shows actual local target processing."""
    stripped = (text or "").strip()
    if len(stripped) < 500:
        return False
    lowered = stripped.lower()
    required_sections = (
        "## local evidence checked",
        "## commands run",
        "## codex attempt before oracle",
        "## verifier/artifact status",
        "## proof obligations still open",
        "## next oracle question",
    )
    if any(section not in lowered for section in required_sections):
        return False
    local_body = _extract_workup_section(stripped, "Local evidence checked")
    commands_body = _extract_workup_section(stripped, "Commands run")
    attempt_body = _extract_workup_section(stripped, "Codex attempt before Oracle")
    artifact_body = _extract_workup_section(stripped, "Verifier/artifact status")
    if len(local_body) < 80 or len(commands_body) < 80 or len(artifact_body) < 80:
        return False
    if len(attempt_body) < 120:
        return False
    command_markers = (
        "```",
        "$ ",
        "python3 ",
        "python ",
        "rg ",
        "find ",
        "git status",
        "sed -n",
        "cat ",
        "ls ",
        "date ",
        "lean ",
        "lake ",
        "sage ",
        "magma ",
        "gap ",
        "node ",
        "npm ",
        "pytest",
        "curl ",
        "unzip ",
        "sha256sum",
    )
    commands_lower = commands_body.lower()
    if not any(marker in commands_lower for marker in command_markers):
        return False
    inspection_markers = (
        "inspected",
        "searched",
        "found",
        "confirmed",
        "checked",
        "ran",
        "replayed",
        "no oracle claim",
        "missing",
        "absent",
    )
    local_artifact_text = f"{local_body}\n{artifact_body}".lower()
    if not any(marker in local_artifact_text for marker in inspection_markers):
        return False
    if not _text_has_codex_attempt(attempt_body):
        return False
    trace_markers = (
        "command",
        "ran",
        "checked",
        "verified",
        "passed",
        "failed",
        "missing",
        "not run",
        "no local",
        "no oracle claim",
        "results.json",
        "verifier",
        "artifact",
        "python",
    )
    return any(marker in lowered for marker in trace_markers)


def _text_has_codex_attempt(text: str) -> bool:
    body = (text or "").strip()
    if len(body) < 120:
        return False
    lowered = body.lower()
    action_markers = (
        "attempted", "tried", "ran", "computed", "checked", "replayed",
        "verified", "constructed", "enumerated", "proved", "reduced",
        "tested", "split", "derived", "bounded", "failed", "blocked",
        "no local replay",
    )
    outcome_markers = (
        "result", "outcome", "therefore", "because", "confirmed", "refuted",
        "mismatch", "counterexample", "obstruction", "blocker", "missing",
        "not present", "timeout", "unsat", "sat", "pass", "fail", "cannot",
        "needs oracle",
    )
    math_or_artifact_markers = (
        "proof", "lemma", "theorem", "bound", "certificate", "construction",
        "verifier", "script", "results.json", "oracle_claim_packet", "cnf",
        "drat", "lrat", "graph", "hash", "sha", "case", "finite",
        "recurrence",
    )
    return (
        any(marker in lowered for marker in action_markers)
        and any(marker in lowered for marker in outcome_markers)
        and any(marker in lowered for marker in math_or_artifact_markers)
    )


def _local_repair_last_has_codex_command_trace(slug: str) -> tuple[bool, str]:
    """Require the last local repair report to include observed Codex commands.

    This prevents a hand-written or stale `codex_workup.md` from serving as a
    ticket into Oracle.  The local repair worker records this trace from Codex's
    JSONL stream after it actually runs target-specific shell commands.
    """
    path = REPO_ROOT_DEFAULT / "tools/community-outreach/targets" / slug / "local_repair_last.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return False, "missing local_repair_last.json"
    except json.JSONDecodeError as exc:
        return False, f"invalid local_repair_last.json: {exc}"
    if not payload.get("ok"):
        return False, "last local repair did not pass"
    postcheck = payload.get("postcheck") if isinstance(payload, dict) else None
    if not isinstance(postcheck, dict):
        return False, "last local repair missing postcheck"
    trace = postcheck.get("codex_command_trace")
    if not isinstance(trace, dict):
        return False, "last local repair missing Codex command trace"
    if not trace.get("ok"):
        return False, str(trace.get("reason") or "Codex command trace not ok")
    if int(trace.get("target_command_count") or 0) <= 0:
        return False, "Codex command trace has no target-local commands"
    substantive = postcheck.get("substantive_local_work")
    if not isinstance(substantive, dict):
        return False, "last local repair missing substantive local-work check"
    if not substantive.get("ok"):
        diagnostics = substantive.get("diagnostics")
        if isinstance(diagnostics, list) and diagnostics:
            return False, "substantive local-work check failed: " + "; ".join(str(item) for item in diagnostics[:4])
        return False, "substantive local-work check failed"
    return True, ""


def _read_codex_next_oracle_question(slug: str, *, max_chars: int = 4000) -> str:
    """Read the exact next Oracle prompt selected by the local Codex workup.

    Newer local-workup runs write next_oracle_question.md.  Older artifacts only
    have a `## Next Oracle question` section inside codex_workup.md, so keep a
    fallback extractor to avoid regressing live targets during rollout.
    """
    workup = _read_target_context_file(
        slug,
        "codex_workup.md",
        max_chars=max(PRE_ORACLE_WORKUP_GATE_CHARS, max_chars),
    )
    if not _codex_workup_has_local_trace(workup):
        return ""
    workup_question = _extract_markdown_section(workup, "Next Oracle question", max_chars=max_chars)
    direct = _read_target_context_file(slug, "next_oracle_question.md", max_chars=max_chars)
    direct = direct.strip()
    if direct:
        direct_path = REPO_ROOT_DEFAULT / "tools/community-outreach/targets" / slug / "next_oracle_question.md"
        workup_path = REPO_ROOT_DEFAULT / "tools/community-outreach/targets" / slug / "codex_workup.md"
        try:
            if workup_question and workup_path.stat().st_mtime > direct_path.stat().st_mtime + 300:
                return workup_question
        except OSError:
            pass
        return direct
    return workup_question


def _is_concrete_next_oracle_question(question: str) -> bool:
    """Reject generic continuation prompts at the dispatch/oracle boundary."""
    q = (question or "").strip()
    if len(q) < 120:
        return False
    lowered = q.lower()
    generic_markers = (
        "continue research",
        "继续研究",
        "do the next step",
        "lower the progress metric",
        "provide metadata",
        "review the board",
        "look into this problem",
        "make progress",
        "find something useful",
    )
    if any(marker in lowered for marker in generic_markers):
        return False
    concrete_markers = (
        "prove",
        "disprove",
        "certificate",
        "construction",
        "counterexample",
        "verifier",
        "exact",
        "bound",
        "obstruction",
        "cnf",
        "lrat",
        "drat",
        "graph",
        "lemma",
        "theorem",
        "compute",
        "enumerate",
        "check",
    )
    return any(marker in lowered for marker in concrete_markers)


def _pre_oracle_codex_workup_status(slug: str) -> tuple[bool, str]:
    """Gate Oracle-deep on an actual local Codex workup.

    The research loop normally runs outreach_local_repair.py before invoking
    this script with --oracle-deep.  Keep the same invariant here because this
    CLI is also used manually and by watchdog/restart paths: Oracle must receive
    a Codex-selected mathematical gap backed by target-local inspection/replay,
    not a board-card metadata restatement.
    """
    workup = _read_target_context_file(
        slug,
        "codex_workup.md",
        max_chars=PRE_ORACLE_WORKUP_GATE_CHARS,
    )
    if not workup.strip():
        return False, "missing codex_workup.md"
    if not _codex_workup_has_local_trace(workup):
        return False, "codex_workup.md lacks required local evidence/commands/verifier/proof-obligation trace"
    trace_ok, trace_reason = _local_repair_last_has_codex_command_trace(slug)
    if not trace_ok:
        return False, trace_reason
    question = _read_codex_next_oracle_question(slug)
    if not _is_concrete_next_oracle_question(question):
        return False, "missing concrete next_oracle_question.md or ## Next Oracle question"
    return True, ""


def _pre_oracle_codex_workup_fresh_after(slug: str, started_at: float) -> tuple[bool, str]:
    """Require the Oracle handoff to be refreshed by the current Codex pass."""
    ok, reason = _pre_oracle_codex_workup_status(slug)
    if not ok:
        return ok, reason
    target_dir = REPO_ROOT_DEFAULT / "tools/community-outreach/targets" / slug
    required = (
        "codex_workup.md",
        "next_oracle_question.md",
        "local_repair_report.md",
    )
    stale: list[str] = []
    threshold = max(0.0, started_at - 2.0)
    for name in required:
        path = target_dir / name
        try:
            mtime = path.stat().st_mtime
        except OSError:
            return False, f"missing {name}"
        if mtime < threshold:
            stale.append(name)
    if stale:
        return False, "stale Codex handoff after current local pass: " + ", ".join(stale)
    return True, ""


def _pre_oracle_codex_workup_recent(slug: str, *, max_age_seconds: int) -> tuple[bool, str]:
    """Accept a just-produced Codex handoff without running the same pass twice."""
    ok, reason = _pre_oracle_codex_workup_status(slug)
    if not ok:
        return ok, reason
    target_dir = REPO_ROOT_DEFAULT / "tools/community-outreach/targets" / slug
    required = (
        "codex_workup.md",
        "next_oracle_question.md",
        "local_repair_report.md",
    )
    oldest_age = 0.0
    for name in required:
        path = target_dir / name
        try:
            age = time.time() - path.stat().st_mtime
        except OSError:
            return False, f"missing {name}"
        oldest_age = max(oldest_age, age)
    if oldest_age > max_age_seconds:
        return False, f"Codex handoff older than reuse window ({oldest_age:.0f}s > {max_age_seconds}s)"
    return True, ""


def _run_pre_oracle_codex_workup(todo_id: str, slug: str, *, timeout: int) -> tuple[bool, str, str]:
    """Run the local Codex worker immediately before Oracle-deep.

    This keeps every Oracle entry point honest.  The research loop already does
    this before calling dispatch_worktree, but watchdog/manual/resume calls can
    also reach --oracle-deep directly.  In all cases the next Oracle prompt
    must come from a fresh target-local Codex replay/workup, not from stale
    metadata or a previous round's generic continuation prompt.
    """
    recent_ok, recent_reason = _pre_oracle_codex_workup_recent(
        slug,
        max_age_seconds=PRE_ORACLE_WORKUP_REUSE_SECONDS,
    )
    if recent_ok:
        return True, "", "recent Codex handoff reused"
    if not LOCAL_REPAIR_SCRIPT_DEFAULT.exists():
        return False, "local repair script missing", str(LOCAL_REPAIR_SCRIPT_DEFAULT)
    log_dir = STATE_DIR_DEFAULT / "research_loop_logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    tag = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = log_dir / f"dispatch_pre_oracle_local_repair_{todo_id}_{tag}.log"
    cmd = [
        "python3",
        str(LOCAL_REPAIR_SCRIPT_DEFAULT),
        "--todo-id",
        todo_id,
        "--timeout",
        str(max(60, min(timeout, 1800))),
        "--json",
    ]
    started = time.time()
    with open(log_path, "ab") as logf:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT_DEFAULT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            rc = proc.wait(timeout=max(90, min(timeout, 2100)))
        except subprocess.TimeoutExpired:
            _terminate_process_group(proc)
            rc = 124
            logf.write(f"\nTIMEOUT after {max(60, min(timeout, 1800))}s; terminated local repair process group\n".encode("utf-8"))
    if rc != 0:
        return False, f"local repair rc={rc}", str(log_path)
    fresh_ok, fresh_reason = _pre_oracle_codex_workup_fresh_after(slug, started)
    if not fresh_ok:
        return False, fresh_reason, str(log_path)
    return True, "", str(log_path)


def _build_deep_initial_prompt(todo: TodoSpec, research_text: str,
                               *, arxiv_hits: list[dict] | None = None,
                               resume_conversation_id: str = "") -> str:
    sub = todo.submission_target()
    profile, _ = load_profile(todo.slug())
    include_arxiv_noise = os.environ.get("OUTREACH_DEEP_INCLUDE_ARXIV", "").lower() in {"1", "true", "yes"}
    research_context_chars = int(os.environ.get("OUTREACH_DEEP_RESEARCH_CONTEXT_CHARS", "1200"))
    codex_workup_chars = int(os.environ.get("OUTREACH_DEEP_CODEX_WORKUP_CHARS", "6000"))
    local_repair_chars = int(os.environ.get("OUTREACH_DEEP_LOCAL_REPAIR_CHARS", "1600"))
    next_oracle_question = _read_codex_next_oracle_question(todo.slug())
    codex_workup = _read_target_context_file(todo.slug(), "codex_workup.md", max_chars=codex_workup_chars)
    local_repair_report = _read_target_context_file(todo.slug(), "local_repair_report.md", max_chars=local_repair_chars)
    parts = [
        "You are the primary mathematical worker on this Omega Project outreach target.",
        "This is not an outreach-copywriting task. The goal is a genuine mathematical contribution.",
        "Codex has already inspected the local workspace before this prompt. Treat the Codex workup as the current local execution state.",
        "Every turn should lower the progress metric, produce a checkable file block, or explicitly re-scope with a useful obstruction.",
        "Stop only when the contract's verifier is satisfied, or when the close/re-scope condition is clearly met.",
        "",
    ]
    if next_oracle_question:
        parts += [
            "## Current Codex-selected task",
            "Codex has already processed the local target directory, inspected the available artifacts, and selected this exact next mathematical gap. Answer this task directly before using board metadata as background.",
            next_oracle_question,
            "",
            "## Codex local workup",
            codex_workup,
            "",
            "## Latest local repair/replay report",
            local_repair_report or "(none yet)",
            "",
        ]
    else:
        raise RuntimeError(
            f"Oracle-deep prompt requested for {todo.todo_id} without a concrete "
            "Codex-selected next_oracle_question backed by local workup"
        )
    parts += [
        "## Compact science contract",
        _compact_science_contract_block(profile),
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
    ]
    if not codex_workup:
        parts += [
            "## Board prior and preliminary attack plan",
            "Prior:",
            todo.prior or "(unknown to the board; survey what you know)",
            "Attack plan:",
            "\n".join(f"- {step}" for step in (todo.attack_plan or [])) or "- (open to your suggestion)",
            "",
        ]
    if resume_conversation_id:
        parts += [
            "## Resume checkpoint",
            f"This is a continuation in existing ChatGPT conversation `{resume_conversation_id}`.",
            "Do not restart from the beginning. Use the previous transcript as context, then push the current science contract forward.",
            "If the previous turn was cut off by network/UI extraction failure, reconstruct the latest useful state from the transcript and continue with the next concrete proof/computation step.",
            "",
        ]
    if include_arxiv_noise and arxiv_hits:
        parts += [
            "## Recent arXiv literature (last 14 days, freshness watch)",
            "Papers whose titles/abstracts overlap our keyword space. **Treat as candidates",
            "for prior-art / first-mover risk, not confirmed competition** — most matches",
            "are coincidental keyword overlap, but skim them and call out any that genuinely",
            "advance our specific sub-goal so we can re-scope if needed.",
            "",
        ]
        for h in arxiv_hits[:8]:
            paper = h.get("paper", {}) if isinstance(h, dict) else {}
            title = (paper.get("title") or "").strip()[:120]
            pub = (paper.get("published") or "")[:10]
            arxiv_id = (paper.get("arxiv_id") or "").strip()
            authors = paper.get("authors", []) or []
            author_str = ", ".join(authors[:3]) + (" et al." if len(authors) > 3 else "")
            matched = ",".join((h.get("matched_keywords") or [])[:5])
            parts.append(
                f"- {arxiv_id} ({pub}) :: {title}\n  authors: {author_str}\n  "
                f"matched=[{matched}], score={h.get('overlap_score','?')}"
            )
        parts.append("")
    if research_text and research_context_chars > 0:
        parts += [
            "## Existing local artifact snapshot",
            "This is clipped background from disk. Treat it as non-authoritative; use it only to avoid repeating prior local work.",
            research_text[:research_context_chars],
            "",
        ]
    loop_state = _read_research_loop_state(todo.slug())
    try:
        no_progress = int(loop_state.get("no_progress_batches") or 0)
        patience = int(loop_state.get("no_progress_patience") or 0)
    except (TypeError, ValueError):
        no_progress = 0
        patience = 0
    if patience > 0 and no_progress >= patience:
        parts += [
            "## Strategy-shift gate",
            f"The outer harness recorded {no_progress}/{patience} recent batches with no artifact-level progress.",
            "Do not continue the same proof sketch or search heuristic.",
            "Pick exactly one of these routes and make it explicit:",
            "- RESCOPE: shrink the target to a publishable lemma/certificate with the same source problem.",
            "- NEW_ATTACK: switch to a different proof/computation strategy and state the new progress metric.",
            "- CLOSE_WITH_OBSTRUCTION: write a concrete failure_analysis.md FILE block explaining the obstruction and what evidence would be needed next.",
            "A strategy shift is not a reason to stop the project; it is the next harness state.",
            "",
        ]
    try:
        from outreach_science_gate import evaluate as science_gate_evaluate  # noqa: PLC0415
        gate = science_gate_evaluate(todo)
        if getattr(gate, "missing", None):
            parts += [
                "## Current deterministic science-gate blockers",
                "The repository gate has already inspected disk artifacts. Do not claim completion until these are fixed on disk or supplied as FILE blocks:",
                "\n".join(f"- {m}" for m in gate.missing),
                "",
                "If a missing artifact is a file, include its exact content in this response using:",
                "FILE: tools/community-outreach/targets/<slug>/<filename>",
                "```<language>",
                "<complete file content>",
                "```",
                "",
            ]
    except Exception:
        pass
    parts += [
        "## Your first turn",
        "Give the first contract-driven research step. Use this exact structure:",
        "  1. CONTRACT TARGET: the precise theorem/counterexample/construction/certificate being attempted.",
        "  2. CURRENT SCORE: the current value/state of the progress metric, or the missing data needed to define it.",
        "  3. MOVE: one concrete proof move, computation, construction edit, or certificate check.",
        "  4. EVIDENCE: what artifact or calculation would verify this move.",
        "  5. NEXT STOP TEST: whether the next turn should write back, continue, or close/re-scope.",
        "Do not summarize the problem back to me. Start doing the mathematics.",
    ]
    return "\n".join(parts)


def _build_deep_resume_prompt(todo: TodoSpec, *, resume_conversation_id: str) -> str:
    """Short continuation prompt for an existing ChatGPT research thread.

    The full initial prompt is intentionally not repeated here. Repeating it
    makes the browser transcript look like a fresh assignment even when the
    server correctly posts to /continue. The existing conversation already has
    the contract, prior turns, and target context; Codex/gates only need to
    tell Oracle what the next concrete move is.
    """
    profile, _ = load_profile(todo.slug())
    next_oracle_question = _read_codex_next_oracle_question(todo.slug())
    blockers: list[str] = []
    try:
        from outreach_science_gate import evaluate as science_gate_evaluate  # noqa: PLC0415
        gate = science_gate_evaluate(todo)
        blockers = list(getattr(gate, "missing", []) or [])[:8]
        next_action = str(getattr(gate, "next_action", "") or "")
        gate_status = str(getattr(gate, "status", "") or "")
    except Exception:
        next_action = ""
        gate_status = ""
    parts = [
        f"Continue from the previous answer in this same conversation `{resume_conversation_id}`.",
        "Do not restart or restate the whole problem. Use the transcript and the existing artifact packet as context.",
        f"Target: {todo.todo_id} · {todo.title}.",
    ]
    if next_oracle_question:
        parts += [
            "",
            "Codex just inspected/replayed the local workspace and selected this exact next Oracle task. Answer it directly.",
            "",
            next_oracle_question,
            "",
            "Respect any local computation stated above. Do not ask for generic metadata or repeat the board card.",
        ]
    if gate_status or next_action:
        parts.append(f"Repository gate now says science_status={gate_status or 'unknown'}, next_action={next_action or 'unknown'}.")
    if blockers:
        parts += [
            "The deterministic gate still needs:",
            "\n".join(f"- {b}" for b in blockers),
        ]
    parts += [
        "Make exactly one next mathematical move that lowers the science-contract progress metric.",
        "Codex has already run the local workup/replay pass when feasible. Use that workup as the execution state; do not ask for generic metadata.",
        "If the last packet is a bounded certificate or obstruction, either strengthen it into a publishable result, produce the missing verifier artifact as FILE blocks, or explain the precise obstruction in a target-specific failure_analysis.md FILE block.",
        "If you find a different meaningful side result, include it as a separate candidate packet rather than replacing this target.",
        "",
        "Compact science contract, for reference:",
        _compact_science_contract_block(profile),
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
    arxiv_stage0: bool = True,
    arxiv_since: str = "14d",
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
        # Stage 0: arXiv freshness sweep (best-effort; never blocks downstream)
        arxiv_summary: dict | None = None
        if arxiv_stage0:
            arxiv_summary = _run_arxiv_watch_for_todo(
                todo, target_log_dir=target_log_dir, since=arxiv_since,
            )
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
        if arxiv_summary is not None:
            analysis["arxiv_stage0"] = arxiv_summary

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
            stage0_hits = (arxiv_summary or {}).get("hits") if arxiv_summary else None
            deep_run = _run_oracle_deep(
                todo, profile, repo_root=repo_root,
                state_dir=state_dir,
                oracle_timeout=oracle_timeout, max_turns=oracle_max_turns,
                write_latex=write_latex,
                codex_driver=codex_driver,
                ship_paper=ship_paper,
                arxiv_hits=stage0_hits,
                resume_conversation_id=_resume_conversation_id(profile.slug, state_dir=state_dir),
            )
            if deep_run is not None:
                analysis["oracle_deep"] = deep_run
                if deep_run.get("skipped"):
                    any_failure = True
                    analysis["stage"] = "ORACLE_DEEP_SKIPPED"
                    analysis["score"] = min(int(analysis.get("score", 0) or 0), 1)
                    analysis.setdefault("findings", [])
                    assert isinstance(analysis["findings"], list)
                    analysis["findings"].insert(
                        0,
                        f"oracle-deep skipped: {deep_run.get('skipped')}",
                    )
                    continue
                materialized = _materialize_oracle_deep_research_md(
                    todo, profile, deep_run, repo_root=repo_root,
                )
                if materialized:
                    analysis["oracle_deep_materialized_research_md"] = materialized
                    # Re-run deterministic analysis after the research artifact
                    # lands so downstream science_gate/research_loop sees the
                    # actual evidence instead of the pre-oracle missing state.
                    refreshed = analyze_supervised_target(todo, profile, repo_root)
                    refreshed["state_json_path"] = analysis.get("state_json_path", "")
                    refreshed["commands_run"] = analysis.get("commands_run", 0)
                    if arxiv_summary is not None:
                        refreshed["arxiv_stage0"] = arxiv_summary
                    refreshed["oracle_deep"] = deep_run
                    refreshed["oracle_deep_materialized_research_md"] = materialized
                    analysis = refreshed

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
                        help="With --oracle-deep, max turns in this single watchdog batch. "
                             "Science/impact gates, not this number, decide whether the target is complete.")
    parser.add_argument("--oracle-timeout", type=int, default=7200,
                        help="Per-turn oracle timeout in seconds (default 7200 = 2h)")
    parser.add_argument("--arxiv-watch", action="store_true",
                        help="Round 0 lit-staleness booster: scan recent arXiv math papers "
                             "against active board targets via NyxID arxiv-api proxy.")
    parser.add_argument("--arxiv-since", default="7d",
                        help="Time window for --arxiv-watch and supervise Stage 0 (default 7d).")
    parser.add_argument("--no-arxiv-stage0", action="store_true",
                        help="Disable the per-target arXiv freshness sweep that runs as Stage 0 "
                             "of --supervise (default: on).")
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
                arxiv_stage0=not args.no_arxiv_stage0,
                arxiv_since=args.arxiv_since,
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
            arxiv_stage0=not args.no_arxiv_stage0,
            arxiv_since=args.arxiv_since,
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
