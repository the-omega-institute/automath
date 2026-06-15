#!/usr/bin/env python3
"""Regression test for independent Oracle closure-check gap feedback."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
MODULE_PATH = REPO / "tools/community-outreach/oracle_consultant.py"


def _load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_consultant_closure_checker_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load oracle_consultant")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    oracle = _load_oracle()

    with tempfile.TemporaryDirectory(dir=MODULE_PATH.parent) as tmp:
        state_dir = Path(tmp) / "state"
        consultant = oracle.OracleConsultant(state_dir=state_dir)
        consultant.logs_dir = Path(tmp) / "logs"
        consultant.logs_dir.mkdir(parents=True)

        class Todo:
            todo_id = "T-CHECK"
            title = "Demo closure target"
            statement = "Prove the demo theorem."

            def slug(self) -> str:
                return "demo_closure"

        prover_prompts: list[str] = []

        def fake_alive() -> bool:
            return True

        def fake_submit_turn(prompt: str, *, conversation_id: str, todo, timeout: int, pdf_path=None):
            idx = len(prover_prompts)
            prover_prompts.append(prompt)
            response_path = consultant.logs_dir / f"prover_{idx}.response.txt"
            if idx == 0:
                response_path.write_text("PROVED. Candidate proof closes the theorem.", encoding="utf-8")
            else:
                response_path.write_text(
                    "The checker gap is now addressed by Lemma A. Further proof details.",
                    encoding="utf-8",
                )
            return oracle.OracleReview(
                todo_id=todo.todo_id,
                title=todo.title,
                task_id=f"prover_{idx}",
                conversation_id=conversation_id or "conv_prover",
                chatgpt_url="https://chatgpt.com/g/g-p-69fdba181e648191a0eb330852658373-openproblem/c/demo",
                submitted_at="2026-01-01T00:00:00+00:00",
                completed_at="2026-01-01T00:00:01+00:00",
                elapsed_seconds=1,
                response_chars=response_path.stat().st_size,
                response_valid=True,
                verdict="",
                score="",
                top_risk="",
                top_recommendation="",
                response_log_path=str(response_path),
                prompt_log_path="",
                is_followup=bool(conversation_id),
                parent_task_id="",
                error="",
            )

        def fake_digest(todo, response_text: str, response_log_path: str = "") -> dict:
            return {
                "science_gate_status": "NEEDS_EVIDENCE",
                "science_gate_missing": [],
                "science_gate_next_action": "deep_reason",
            }

        def fake_eval(turn, last_response, all_turns, objective, *, todo=None, timeout_s=300):
            if turn == 0:
                return {
                    "contribution": "candidate proof",
                    "verdict": "complete",
                    "verdict_reason": "candidate proof claims closure",
                    "next_question": "",
                }
            return {
                "contribution": "followed checker gap",
                "verdict": "continue",
                "verdict_reason": "keep going",
                "next_question": "",
            }

        def fake_checker(*_args, **_kwargs):
            return {
                "ok": True,
                "closed": False,
                "verdict": "NOT_CLOSED",
                "gap": "Lemma A is stated but not proved.",
                "response": "CHECKER_VERDICT: NOT_CLOSED\nMINIMAL_GAP: Lemma A is stated but not proved.",
            }

        old_alive = consultant.is_alive
        old_submit_turn = consultant._submit_turn
        old_checker = consultant._closure_check_turn
        old_digest = oracle._codex_digest_oracle_turn
        old_replay = oracle._run_local_codex_replay_after_oracle
        old_eval = oracle.codex_evaluate_progress
        old_missing = oracle._science_gate_missing_for_todo
        old_closure_enabled = oracle.ORACLE_CLOSURE_CHECK_ENABLED
        try:
            consultant.is_alive = fake_alive
            consultant._submit_turn = fake_submit_turn
            consultant._closure_check_turn = fake_checker
            oracle._codex_digest_oracle_turn = fake_digest
            oracle._run_local_codex_replay_after_oracle = lambda *_args, **_kwargs: {"ok": True}
            oracle.codex_evaluate_progress = fake_eval
            oracle._science_gate_missing_for_todo = lambda _todo: []
            oracle.ORACLE_CLOSURE_CHECK_ENABLED = True
            run = consultant.deep_reasoning(
                Todo(),
                "initial prompt",
                max_turns=2,
                per_turn_timeout=1,
                slug="demo_closure",
            )
        finally:
            consultant.is_alive = old_alive
            consultant._submit_turn = old_submit_turn
            consultant._closure_check_turn = old_checker
            oracle._codex_digest_oracle_turn = old_digest
            oracle._run_local_codex_replay_after_oracle = old_replay
            oracle.codex_evaluate_progress = old_eval
            oracle._science_gate_missing_for_todo = old_missing
            oracle.ORACLE_CLOSURE_CHECK_ENABLED = old_closure_enabled

        if len(run.get("turns") or []) != 2:
            raise AssertionError(f"checker gap should force a second prover turn: {run}")
        if run["turns"][0].get("oracle_closure_check", {}).get("closed") is not False:
            raise AssertionError(f"first turn did not record checker rejection: {run['turns'][0]}")
        if "Lemma A is stated but not proved" not in prover_prompts[1]:
            raise AssertionError(f"checker gap was not fed back to prover: {prover_prompts[1]!r}")
        if run.get("final_verdict") == "BREAKTHROUGH":
            raise AssertionError(f"checker rejection should prevent immediate breakthrough: {run}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
