"""Tests for the deterministic split-overlap harness."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

SCRIPT_ROOT = Path(__file__).resolve().parents[1]
import sys

sys.path.insert(0, str(SCRIPT_ROOT))

import split_overlap_harness as harness  # noqa: E402


CURRENT_BODY = r"""
\title{Current threshold paper}
\begin{abstract}
We prove a Fibonacci finite-window fold theorem.
\end{abstract}
\begin{theorem}\label{thm:current}
The sliding overlap reconstruction has a sharp m >= 3 threshold. It gives
finite-memory conjugacy with an explicit residue window decoder and identifies
the Fischer cover.
\end{theorem}
"""


SIBLING_BODY = r"""
\title{Old submitted paper}
\begin{abstract}
This submitted paper studies Zeckendorf normalization and Fold_m.
\end{abstract}
\begin{theorem}\label{thm:old}
Overlapping windows recover the input for m >= 3. The theorem gives a finite
memory inverse, congruence residue decoder, and the right Fischer cover of the
image shift.
\end{theorem}
"""


UNRELATED_BODY = r"""
\title{Unrelated paper}
\begin{abstract}
This paper studies a homological visibility obstruction.
\end{abstract}
\begin{theorem}\label{thm:unrelated}
For a finite diagram of visible quotients, the pullback obstruction vanishes
exactly when the corresponding comparison map is an isomorphism.
\end{theorem}
"""


class SplitOverlapHarnessTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.pub = self.root / "papers" / "publication"
        self.pub.mkdir(parents=True)
        self.board = self.pub / "PROGRAM_BOARD.md"

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def _write_paper(self, name: str, body: str) -> Path:
        paper = self.pub / name
        paper.mkdir()
        (paper / "main.tex").write_text(body, encoding="utf-8")
        return paper

    def _write_board(self, old_status: str, old_note: str = "") -> None:
        self.board.write_text(
            "\n".join(
                [
                    "# Program Board",
                    "",
                    "| dir | journal | status | reroute |",
                    "|---|---|---|---|",
                    "| `2026_current_overlap` | DCDS-A | C-DONE | -- |",
                    f"| `submitted_2026_old_overlap` | Fibonacci Q. | {old_status} | {old_note} |",
                    "| `2026_unrelated` | APAL | B-0 | -- |",
                ]
            ),
            encoding="utf-8",
        )

    def _write_custom_board(self, rows: list[tuple[str, str, str, str]]) -> None:
        self.board.write_text(
            "\n".join(
                [
                    "# Program Board",
                    "",
                    "| dir | journal | status | reroute |",
                    "|---|---|---|---|",
                    *[
                        f"| `{name}` | {journal} | {status} | {reroute} |"
                        for name, journal, status, reroute in rows
                    ],
                ]
            ),
            encoding="utf-8",
        )

    def test_unresolved_prior_submission_defers_later_active_draft(self) -> None:
        current = self._write_paper("2026_current_overlap", CURRENT_BODY)
        self._write_paper("submitted_2026_old_overlap", SIBLING_BODY)
        self._write_paper("2026_unrelated", UNRELATED_BODY)
        self._write_board("\u62d2\u7a3f 05-01")

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=current,
            min_shared_markers=3,
        )

        self.assertTrue(report["gate_failed"])
        self.assertEqual(report["summary"]["deferred_wait_for_prior_submission"], 1)
        self.assertEqual(len(report["findings"]), 1)
        finding = report["findings"][0]
        self.assertEqual(finding["classification"], "deferred_wait_for_prior_submission")
        self.assertEqual(finding["paper_a"], "2026_current_overlap")
        self.assertEqual(finding["paper_b"], "submitted_2026_old_overlap")
        self.assertEqual(finding["primary_paper"], "submitted_2026_old_overlap")
        self.assertEqual(finding["deferred_paper"], "2026_current_overlap")
        self.assertEqual(
            finding["recommended_action"],
            "defer_later_draft_until_prior_submission_feedback",
        )
        self.assertIn("m_ge_3_threshold", finding["shared_claim_markers"])

    def test_submitted_marker_file_defers_later_active_draft(self) -> None:
        current = self._write_paper("2026_current_overlap", CURRENT_BODY)
        prior = self._write_paper("2026_old_overlap", SIBLING_BODY)
        (prior / "SUBMITTED").write_text("Submitted to Fibonacci Q.\n", encoding="utf-8")
        self._write_board("C-DONE")

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=current,
            min_shared_markers=3,
        )

        self.assertTrue(report["gate_failed"])
        finding = report["findings"][0]
        self.assertEqual(finding["classification"], "deferred_wait_for_prior_submission")
        self.assertEqual(finding["primary_paper"], "2026_old_overlap")
        self.assertEqual(finding["deferred_paper"], "2026_current_overlap")

    def test_current_prior_submission_is_not_blocked_by_later_deferred_draft(self) -> None:
        self._write_paper("2026_current_overlap", CURRENT_BODY)
        prior = self._write_paper("submitted_2026_old_overlap", SIBLING_BODY)
        self._write_board("\u5df2\u6295 04-30 \u5ba1\u7a3f\u4e2d")

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=prior,
            min_shared_markers=3,
        )

        self.assertFalse(report["gate_failed"])
        self.assertEqual(report["summary"]["deferred_wait_for_prior_submission"], 1)
        finding = report["findings"][0]
        self.assertEqual(finding["primary_paper"], "submitted_2026_old_overlap")
        self.assertEqual(finding["deferred_paper"], "2026_current_overlap")

    def test_two_submitted_overlaps_use_explicit_submission_dates(self) -> None:
        later = self._write_paper("2026_current_overlap", CURRENT_BODY)
        self._write_paper("submitted_2026_old_overlap", SIBLING_BODY)
        self._write_custom_board(
            [
                ("2026_current_overlap", "DCDS-A", "\u5df2\u6295 05-11", "--"),
                ("submitted_2026_old_overlap", "JNT", "\u5df2\u6295 04-07", "--"),
            ]
        )

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=later,
            min_shared_markers=3,
        )

        self.assertTrue(report["gate_failed"])
        finding = report["findings"][0]
        self.assertEqual(finding["classification"], "deferred_wait_for_prior_submission")
        self.assertEqual(finding["primary_paper"], "submitted_2026_old_overlap")
        self.assertEqual(finding["deferred_paper"], "2026_current_overlap")
        self.assertEqual(finding["submission_date_a"], "2026-05-11")
        self.assertEqual(finding["submission_date_b"], "2026-04-07")

    def test_earlier_current_submission_is_not_blocked_by_later_submitted_archive(self) -> None:
        earlier = self._write_paper("2026_current_overlap", CURRENT_BODY)
        self._write_paper("submitted_2026_old_overlap", SIBLING_BODY)
        self._write_custom_board(
            [
                ("2026_current_overlap", "DCDS-A", "\u5df2\u6295 04-07", "--"),
                ("submitted_2026_old_overlap", "JNT", "\u5df2\u6295 05-11", "--"),
            ]
        )

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=earlier,
            min_shared_markers=3,
        )

        self.assertFalse(report["gate_failed"])
        finding = report["findings"][0]
        self.assertEqual(finding["classification"], "deferred_wait_for_prior_submission")
        self.assertEqual(finding["primary_paper"], "2026_current_overlap")
        self.assertEqual(finding["deferred_paper"], "submitted_2026_old_overlap")

    def test_explicitly_closed_sibling_is_resolved_not_blocking(self) -> None:
        current = self._write_paper("2026_current_overlap", CURRENT_BODY)
        self._write_paper("submitted_2026_old_overlap", SIBLING_BODY)
        self._write_board(
            "\u62d2\u7a3f 05-01; \u8def\u7ebf\u5173\u95ed; \u4e0d\u56de Stage A",
            "core merged into current paper",
        )

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=current,
            min_shared_markers=3,
        )

        self.assertFalse(report["gate_failed"])
        self.assertEqual(report["summary"]["resolved"], 1)
        self.assertEqual(report["findings"][0]["classification"], "resolved")

    def test_report_only_cli_writes_json_and_returns_zero(self) -> None:
        current = self._write_paper("2026_current_overlap", CURRENT_BODY)
        self._write_paper("submitted_2026_old_overlap", SIBLING_BODY)
        self._write_board("\u62d2\u7a3f 05-01")
        report_dir = self.root / "reports"

        rc = harness.main(
            [
                "--publication-dir",
                str(self.pub),
                "--board",
                str(self.board),
                "--current-paper",
                str(current),
                "--report-dir",
                str(report_dir),
                "--min-shared-markers",
                "3",
                "--report-only",
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue((report_dir / "split_overlap_report.json").exists())
        self.assertTrue((report_dir / "split_overlap_report.md").exists())

    def test_shared_broad_markers_without_bundle_are_informational(self) -> None:
        current = self._write_paper(
            "2026_current_overlap",
            r"""
            \title{Finite zeta branch paper}
            \begin{abstract}
            We study dynamical zeta finite parts for shifts of finite type,
            an m=2 branch locus, a residue window decoder, and spectral
            rigidity in a cyclic model.
            \end{abstract}
            \begin{theorem}\label{thm:a}
            The finite-state zeta certificate has a residue window decoder
            and a spectral rigidity conclusion for a cyclic m=2 branch model.
            \end{theorem}
            """,
        )
        self._write_paper(
            "submitted_2026_old_overlap",
            r"""
            \title{Different spectral residue paper}
            \begin{abstract}
            This submitted manuscript also mentions dynamical zeta finite
            parts for a shift of finite type, m=2 branch geometry, a residue
            window decoder, and spectral rigidity, but proves a different
            determinant statement.
            \end{abstract}
            \begin{theorem}\label{thm:b}
            A determinant family with m=2 branch symmetry admits a residue
            window decoder and a spectral rigidity estimate.
            \end{theorem}
            """,
        )
        self._write_board("\u62d2\u7a3f 05-01")

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=current,
            min_shared_markers=3,
        )

        self.assertFalse(report["gate_failed"])
        self.assertEqual(report["summary"]["informational"], 1)
        self.assertEqual(report["findings"][0]["classification"], "informational")

    def test_shared_latex_enumerate_template_does_not_block(self) -> None:
        current = self._write_paper(
            "2026_current_overlap",
            r"""
            \title{Current list-shaped theorem}
            \begin{theorem}\label{thm:a}
            The boundary operator satisfies
            \begin{enumerate}[label=(\roman*),leftmargin=*,itemsep=2pt]
            \item a local estimate;
            \item a trace estimate;
            \end{enumerate}
            for cubical forms.
            \end{theorem}
            """,
        )
        self._write_paper(
            "submitted_2026_old_overlap",
            r"""
            \title{Old list-shaped theorem}
            \begin{theorem}\label{thm:b}
            The Markov observable satisfies
            \begin{enumerate}[label=(\roman*),leftmargin=*,itemsep=2pt]
            \item a cylinder estimate;
            \item a pressure estimate;
            \end{enumerate}
            for a one-step chain.
            \end{theorem}
            """,
        )
        self._write_board("\u62d2\u7a3f 05-01")

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=current,
            min_shared_markers=3,
        )

        self.assertFalse(report["gate_failed"])

    def test_exact_duplicate_active_drafts_need_human_resolution(self) -> None:
        current = self._write_paper("2026_current_overlap", UNRELATED_BODY)
        self._write_paper("2026_unrelated", UNRELATED_BODY)
        self._write_board("\u62d2\u7a3f 05-01")

        report = harness.build_overlap_report(
            publication_dir=self.pub,
            board_path=self.board,
            current_paper=current,
            min_shared_markers=3,
        )

        self.assertTrue(report["gate_failed"])
        finding = report["findings"][0]
        self.assertEqual(finding["classification"], "needs_human_resolution")
        self.assertTrue(finding["evidence"]["exact_source_duplicate"])


if __name__ == "__main__":
    unittest.main()
