#!/usr/bin/env python3
"""Self-tests for the printed Stage-A Horn closure checker."""

from __future__ import annotations

import unittest

from stage_a_horn_closure_checker import (
    BranchBaseError,
    branch_stability_report,
    closure_projection,
    load_printed_system,
)


class StageAHornClosureCheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.system = load_printed_system()

    def test_three_printed_branches_have_exact_coordinate_projections(self) -> None:
        self.assertEqual(
            closure_projection(self.system, "A_rec"),
            [],
        )
        self.assertEqual(
            closure_projection(self.system, "A_scan"),
            ["qraw"],
        )
        self.assertEqual(
            closure_projection(self.system, "A_plus"),
            ["qraw", "qrgs"],
        )

    def test_raw_coordinate_uses_single_canonical_atom(self) -> None:
        self.assertIn("qraw", self.system.coordinates)
        for legacy in ("qinv", "qlex", "q raw", "q_raw"):
            self.assertNotIn(legacy, self.system.coordinates)

    def test_coordinate_atoms_are_rejected_from_base_inputs(self) -> None:
        bad_atoms = set(self.system.branches["A_rec"])
        bad_atoms.add("qrgs")
        with self.assertRaises(BranchBaseError):
            closure_projection(self.system, bad_atoms)

    def test_branch_stability_absences_are_closure_level(self) -> None:
        report = branch_stability_report(self.system)
        for branch in ("A_rec", "A_scan", "A_plus"):
            self.assertEqual(report[branch]["unexpected_present_in_closure"], [])
            self.assertEqual(report[branch]["unexpected_rule_heads"], [])
        self.assertIn("scanOK", report["A_rec"]["expected_absent_from_closure"])
        self.assertIn("ScriptOKstage_a", report["A_scan"]["expected_absent_from_closure"])


if __name__ == "__main__":
    unittest.main()
