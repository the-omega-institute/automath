"""Tests for the three new PI autonomous_actions.

Each guarded action gets a positive case + a guard-rejection case.
The action log file is redirected to a tmp_path to keep test isolation.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
PI_PATH = ROOT / "tools" / "chatgpt-oracle" / "pi_review.py"


@pytest.fixture
def pi(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location("pi_review_under_test", PI_PATH)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["pi_review_under_test"] = mod
    spec.loader.exec_module(mod)
    monkeypatch.setattr(mod, "_PI_ACTION_LOG", tmp_path / ".pi_action_log.json")
    return mod


def _write_state(state_dir: Path, name: str, **fields) -> Path:
    state_dir.mkdir(parents=True, exist_ok=True)
    p = state_dir / f"{name}.json"
    base = {
        "paper_name": name,
        "target_journal": "Old Journal",
        "stage_b_verdicts": [],
        "stage_b_issue_streaks": {},
        "retarget_history": [],
    }
    base.update(fields)
    p.write_text(json.dumps(base) + "\n", encoding="utf-8")
    return p


def test_force_b_stuck_block_rejects_unknown_reason(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    _write_state(state_dir, "paper_x")
    res = pi._execute_force_b_stuck_block(
        {"paper": "paper_x", "reason": "WHATEVER"}, state_dir)
    assert res.startswith("rejected")


def test_force_b_stuck_block_accepts_valid_reason(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    p = _write_state(state_dir, "paper_x", stage_b_passed=True)
    res = pi._execute_force_b_stuck_block(
        {"paper": "paper_x", "reason": "B_STUCK_JOURNAL_FIT"}, state_dir)
    d = json.loads(p.read_text(encoding="utf-8"))
    assert "forced" in res
    assert d["block_reason"] == "B_STUCK_JOURNAL_FIT"
    assert d["stage_b_passed"] is False


def test_trigger_retarget_rejects_when_guard_fails(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    _write_state(state_dir, "paper_x",
                 stage_b_verdicts=["minor revision", "minor revision"])
    res = pi._execute_trigger_retarget(
        {"paper": "paper_x"}, state_dir)
    assert res.startswith("rejected")


def test_trigger_retarget_accepts_on_fit_streak(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    p = _write_state(state_dir, "paper_x",
                     stage_b_issue_streaks={"__journal_fit__": 2},
                     stage_b_verdicts=["reject", "reject"],
                     current_stage="B")
    res = pi._execute_trigger_retarget(
        {"paper": "paper_x", "new_target_journal": "Exp. Math"}, state_dir)
    d = json.loads(p.read_text(encoding="utf-8"))
    assert "retargeted" in res
    assert d["current_stage"] == "F"
    assert d["target_journal"] == "Exp. Math"
    assert len(d["retarget_history"]) == 1


def test_trigger_retarget_caps_at_two(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    _write_state(state_dir, "paper_x",
                 retarget_history=[{"x": 1}, {"x": 2}])
    res = pi._execute_trigger_retarget({"paper": "paper_x"}, state_dir)
    assert "max retargets" in res


def test_requeue_focused_patch_rejects_low_streak(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    _write_state(state_dir, "paper_x",
                 stage_b_issue_streaks={"prop. 4.35": 1})
    res = pi._execute_requeue_focused_patch(
        {"paper": "paper_x", "canonical_key": "prop. 4.35"}, state_dir)
    assert res.startswith("rejected")


def test_requeue_focused_patch_rate_limit(pi, tmp_path):
    state_dir = tmp_path / "pipeline_state"
    _write_state(state_dir, "paper_x",
                 stage_b_issue_streaks={"prop. 4.35": 3})
    res1 = pi._execute_requeue_focused_patch(
        {"paper": "paper_x", "canonical_key": "prop. 4.35"}, state_dir)
    assert "requeued" in res1
    res2 = pi._execute_requeue_focused_patch(
        {"paper": "paper_x", "canonical_key": "prop. 4.35"}, state_dir)
    assert "rate-limited" in res2
