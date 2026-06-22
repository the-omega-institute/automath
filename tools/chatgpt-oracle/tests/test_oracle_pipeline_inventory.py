from __future__ import annotations

import sys
import tempfile
import unittest
import json
from pathlib import Path
from unittest import mock

SCRIPT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_ROOT))

import oracle_pipeline  # noqa: E402


class OraclePipelineInventoryTests(unittest.TestCase):
    def test_inventory_coverage_rows_are_added_for_omitted_tex_labels(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp)
            (paper_path / "main.tex").write_text(
                r"""
\begin{theorem}[Kept]
\label{thm:kept}
Kept theorem.
\end{theorem}

\begin{proposition}[Omitted]
\label{prop:omitted}
Omitted proposition.
\end{proposition}
""",
                encoding="utf-8",
            )
            inventory = {
                "valid": True,
                "in_scope_present": [
                    {
                        "label": "thm:kept",
                        "location": "main.tex:2",
                        "reason": "already present",
                        "required_action": "keep",
                    }
                ],
                "missing_in_scope_results": [],
                "weak_in_scope_core_results": [],
                "proof_gaps": [],
                "supporting_appendix_or_background": [],
                "out_of_scope_strong_results": [],
                "split_candidates": [],
                "irrelevant_or_remove": [],
                "naive_truncation_risks": [],
                "journal_style_gaps": [],
            }

            updated = oracle_pipeline._ensure_inventory_label_coverage(
                paper_path, inventory
            )

        labels = "\n".join(
            str(row.get("label", ""))
            for row in updated["in_scope_present"]
            if isinstance(row, dict)
        )
        self.assertIn("thm:kept", labels)
        self.assertIn("prop:omitted", labels)
        self.assertEqual(updated["missing_in_scope_results"], [])
        self.assertEqual(updated["proof_gaps"], [])

    def test_windows_tool_hint_is_converted_for_wsl_paths(self):
        converted = oracle_pipeline._windows_path_hint_for_current_platform(
            r"C:\Users\zwl62\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe"
        )

        if oracle_pipeline.sys.platform == "win32":
            self.assertEqual(
                converted,
                r"C:\Users\zwl62\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe",
            )
        else:
            self.assertEqual(
                converted,
                "/mnt/c/Users/zwl62/AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdflatex.exe",
            )

    def test_find_latex_tool_uses_wsl_converted_windows_hint(self):
        original_which = oracle_pipeline.shutil.which
        original_hints = oracle_pipeline.WINDOWS_LATEX_TOOL_HINTS
        original_bin_dirs = oracle_pipeline.WINDOWS_LATEX_BIN_DIRS
        with tempfile.TemporaryDirectory() as tmp:
            candidate = Path(tmp) / "pdflatex.exe"
            candidate.write_text("", encoding="utf-8")
            oracle_pipeline.shutil.which = lambda _name: None
            oracle_pipeline.WINDOWS_LATEX_BIN_DIRS = ()
            oracle_pipeline.WINDOWS_LATEX_TOOL_HINTS = {
                "pdflatex": (str(candidate),)
            }
            try:
                self.assertEqual(
                    oracle_pipeline.find_latex_tool("pdflatex"),
                    str(candidate),
                )
            finally:
                oracle_pipeline.shutil.which = original_which
                oracle_pipeline.WINDOWS_LATEX_TOOL_HINTS = original_hints
                oracle_pipeline.WINDOWS_LATEX_BIN_DIRS = original_bin_dirs

    def test_git_commit_reports_git_add_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp) / "paper"
            paper_path.mkdir()
            (paper_path / "main.tex").write_text("changed", encoding="utf-8")

            def fake_run_cmd(cmd, **_kwargs):
                if cmd[:2] == ["git", "diff"]:
                    return oracle_pipeline.subprocess.CompletedProcess(
                        cmd, 0, stdout="", stderr=""
                    )
                if cmd[:2] == ["git", "add"]:
                    return oracle_pipeline.subprocess.CompletedProcess(
                        cmd,
                        128,
                        stdout="",
                        stderr="fatal: Unable to create '.git/index.lock': File exists.",
                    )
                return oracle_pipeline.subprocess.CompletedProcess(
                    cmd, 0, stdout="", stderr=""
                )

            with mock.patch.object(oracle_pipeline, "run_cmd", side_effect=fake_run_cmd):
                with self.assertRaises(RuntimeError) as ctx:
                    oracle_pipeline.git_commit(
                        paper_path, "stage-A R1: weak_in_scope_core_results"
                    )

        self.assertIn("git add failed", str(ctx.exception))
        self.assertIn("index.lock", str(ctx.exception))

    def test_theoremization_prompt_includes_active_oracle_labels(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp)
            (paper_path / "oracle_stage_a_escalation.json").write_text(
                json.dumps(
                    {
                        "verdict": "rerun_stage_a",
                        "publishable_route": True,
                        "core_theorem_direction": "insert exact theorem spine",
                        "codex_instructions": [
                            "Insert theorem label thm:finite-antichain-basis.",
                            "Insert theorem label thm:canonical-bad-subrecord-classifier.",
                            "Insert theorem label thm:stage-a-real-block-discharge.",
                            "Insert corollary label cor:current-stage-a-closure-criterion.",
                        ],
                    }
                ),
                encoding="utf-8",
            )

            prompt = oracle_pipeline.build_theoremization_prompt(
                str(paper_path),
                "CICM",
                "missing_in_scope_results",
                '[{"label":"oracle-required","required_action":"add package"}]',
                1,
            )

        self.assertIn("Active Oracle Stage A directive", prompt)
        self.assertIn("thm:finite-antichain-basis", prompt)
        self.assertIn("thm:canonical-bad-subrecord-classifier", prompt)
        self.assertIn("thm:stage-a-real-block-discharge", prompt)
        self.assertIn("cor:current-stage-a-closure-criterion", prompt)
        self.assertIn("A run that leaves those labels absent is a failed Stage A2 edit", prompt)

    def test_active_oracle_required_labels_are_recognized_when_already_proved(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp)
            (paper_path / "oracle_stage_a_escalation.json").write_text(
                json.dumps(
                    {
                        "verdict": "rerun_stage_a",
                        "publishable_route": True,
                        "required_theorem_package": [
                            "Require theorem label thm:finite-audit-antichain-basis.",
                            "Require corollary label cor:current-stage-a-closure-exactness.",
                        ],
                        "codex_instructions": [
                            "If exact labels already exist with proof environments, "
                            "recognize and synchronize the Stage A inventory instead "
                            "of duplicating thm:finite-audit-antichain-basis and "
                            "cor:current-stage-a-closure-exactness."
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (paper_path / "main.tex").write_text(
                r"""
\begin{theorem}[Finite audit antichain basis]
\label{thm:finite-audit-antichain-basis}
Every admissible finite audit obstruction has a finite antichain basis.
\end{theorem}
\begin{proof}
Use the finite record preorder and choose the minimal bad records.
\end{proof}

\begin{corollary}[Current Stage A closure exactness]
\label{cor:current-stage-a-closure-exactness}
The current Stage A closure certificate is exact for the recognized basis.
\end{corollary}
\begin{proof}
Apply the preceding theorem and unfold the recorded closure certificate.
\end{proof}
""",
                encoding="utf-8",
            )

            recognized, detail = oracle_pipeline._active_oracle_required_labels_recognized(
                paper_path
            )

        self.assertTrue(recognized, detail)
        self.assertIn("thm:finite-audit-antichain-basis", detail)
        self.assertIn("cor:current-stage-a-closure-exactness", detail)

    def test_active_oracle_recognition_artifacts_are_stageable(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp)
            review_bundle = paper_path / "review_bundle"
            review_bundle.mkdir()
            (paper_path / "oracle_stage_a_escalation.json").write_text(
                json.dumps(
                    {
                        "verdict": "rerun_stage_a",
                        "codex_instructions": [
                            "If all five labels exist, synchronize theorem_inventory.md, "
                            "theorem_inventory.json, stage_a_audit.json, and "
                            "submission_abstract.tex by exact label and title.",
                            "Regenerate final digest after exact label-level recognition.",
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (paper_path / "theorem_inventory.json").write_text("{}", encoding="utf-8")
            (paper_path / "theorem_inventory.md").write_text("inventory", encoding="utf-8")
            (paper_path / "stage_a_audit.json").write_text("{}", encoding="utf-8")
            (review_bundle / "FINAL_DIGESTS_SHA256.md").write_text("digest", encoding="utf-8")

            files = {
                Path(raw).name
                for raw in oracle_pipeline._paper_source_files(paper_path)
            }
            raw_files = set(oracle_pipeline._paper_source_files(paper_path))

        self.assertIn("theorem_inventory.json", files)
        self.assertIn("theorem_inventory.md", files)
        self.assertIn("stage_a_audit.json", files)
        self.assertTrue(
            any(raw.endswith("review_bundle/FINAL_DIGESTS_SHA256.md")
                or raw.endswith("review_bundle\\FINAL_DIGESTS_SHA256.md")
                for raw in raw_files)
        )

    def test_active_oracle_recognition_artifacts_are_force_added_when_ignored(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp)
            review_bundle = paper_path / "review_bundle"
            review_bundle.mkdir()
            (paper_path / "oracle_stage_a_escalation.json").write_text(
                json.dumps(
                    {
                        "verdict": "rerun_stage_a",
                        "codex_instructions": [
                            "Synchronize theorem_inventory.md, theorem_inventory.json, "
                            "stage_a_audit.json, and final digest by exact label recognition."
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (paper_path / "main.tex").write_text("source", encoding="utf-8")
            (paper_path / "theorem_inventory.json").write_text("{}", encoding="utf-8")
            (paper_path / "stage_a_audit.json").write_text("{}", encoding="utf-8")

            commands = []

            def fake_run_cmd(cmd, **_kwargs):
                commands.append(cmd)
                return oracle_pipeline.subprocess.CompletedProcess(
                    cmd, 0, stdout="", stderr=""
                )

            with mock.patch.object(oracle_pipeline, "run_cmd", side_effect=fake_run_cmd):
                oracle_pipeline._add_paper_only(paper_path)

        forced_adds = [cmd for cmd in commands if cmd[:3] == ["git", "add", "-f"]]
        normal_adds = [cmd for cmd in commands if cmd[:2] == ["git", "add"] and "-f" not in cmd]
        self.assertTrue(forced_adds)
        self.assertTrue(
            any("theorem_inventory.json" in " ".join(cmd) for cmd in forced_adds)
        )
        self.assertTrue(
            any("stage_a_audit.json" in " ".join(cmd) for cmd in forced_adds)
        )
        self.assertTrue(any("main.tex" in " ".join(cmd) for cmd in normal_adds))

    def test_verified_manual_patch_revives_oracle_park(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper_path = Path(tmp)
            review_bundle = paper_path / "review_bundle"
            review_bundle.mkdir()
            (paper_path / "oracle_stage_a_escalation.json").write_text(
                json.dumps(
                    {
                        "verdict": "park",
                        "publishable_route": True,
                        "park_reason": (
                            "route parked until a manual source patch can add "
                            "and verify the missing theorem package"
                        ),
                        "codex_instructions": [
                            "The parked manuscript may be revived only by a "
                            "source-first manual patch.",
                            "Closure criterion: proceed is allowed only if all "
                            "five theorem/corollary environments are present "
                            "with proofs and recognized by all inventory, "
                            "stage_a_audit, and verifier outputs.",
                        ],
                    }
                ),
                encoding="utf-8",
            )
            verifier = review_bundle / "verify_stage_a_audit.py"
            verifier.write_text("print('ok')\n", encoding="utf-8")

            def fake_run(cmd, **_kwargs):
                return oracle_pipeline.subprocess.CompletedProcess(
                    cmd, 0, stdout='{"errors":[],"exit_code":0}', stderr=""
                )

            with mock.patch.object(oracle_pipeline.subprocess, "run", side_effect=fake_run):
                active, detail = oracle_pipeline._stage_a_manual_patch_revive_active(
                    paper_path
                )

        self.assertTrue(active, detail)
        self.assertIn("verify_stage_a_audit.py passed", detail)

    def test_stage_a_audit_accepts_verified_resolved_proceed_record(self):
        audit = {
            "metrics": {
                "theorem_completeness": 9,
                "proof_integrity": 8,
                "depth_novelty": 7,
                "scope_coverage": 9,
                "journal_fit": 7,
                "split_hygiene": 9,
            },
            "verdict": "proceed",
            "audit_unparseable": False,
            "blockers": [],
            "split_required": False,
            "ready_for_oracle_review": True,
            "resolved_blocks": [
                {
                    "block_id": "stage_a_audit_real_block",
                    "status": "resolved_by_theorem_package",
                    "remaining_absent_coordinates": [],
                }
            ],
        }

        self.assertTrue(oracle_pipeline.stage_a_audit_passes(audit))

    def test_negative_boundary_missing_items_do_not_trigger_theoremization(self):
        inventory = {
            "valid": True,
            "in_scope_present": [],
            "missing_in_scope_results": [
                {
                    "label": "missing:fresh-newmath-lean-rebuild-and-axiom-audit",
                    "reason": "qsrc negative",
                    "required_action": "keep missing",
                },
                {
                    "label": "missing:external-upload-or-archive-coordinate",
                    "reason": "qext negative",
                    "required_action": "do not claim",
                },
            ],
            "weak_in_scope_core_results": [],
            "proof_gaps": [],
            "supporting_appendix_or_background": [],
            "out_of_scope_strong_results": [],
            "split_candidates": [],
            "irrelevant_or_remove": [],
            "naive_truncation_risks": [],
            "journal_style_gaps": [],
        }

        action, items = oracle_pipeline._inventory_action(inventory)

        self.assertEqual(action, "")
        self.assertEqual(items, [])

    def test_real_missing_items_still_trigger_theoremization(self):
        inventory = {
            "valid": True,
            "in_scope_present": [],
            "missing_in_scope_results": [
                {
                    "label": "missing:central-theorem",
                    "reason": "scope contract requires a central theorem",
                    "required_action": "add theorem and proof",
                },
                {
                    "label": "missing:external-upload-or-archive-coordinate",
                    "reason": "qext negative",
                    "required_action": "do not claim",
                },
            ],
            "weak_in_scope_core_results": [],
            "proof_gaps": [],
            "supporting_appendix_or_background": [],
            "out_of_scope_strong_results": [],
            "split_candidates": [],
            "irrelevant_or_remove": [],
            "naive_truncation_risks": [],
            "journal_style_gaps": [],
        }

        action, items = oracle_pipeline._inventory_action(inventory)

        self.assertEqual(action, "missing_in_scope_results")
        self.assertEqual(len(items), 1)
        self.assertEqual(items[0]["label"], "missing:central-theorem")


if __name__ == "__main__":
    unittest.main()
