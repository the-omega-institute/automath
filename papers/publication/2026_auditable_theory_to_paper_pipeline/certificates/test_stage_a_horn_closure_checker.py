#!/usr/bin/env python3
"""Self-tests for the printed Stage-A Horn closure checker."""

from __future__ import annotations

import unittest

from stage_a_horn_closure_checker import (
    BranchBaseError,
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
            ["qinv"],
        )
        self.assertEqual(
            closure_projection(self.system, "A_plus"),
            ["qinv", "qrgs"],
        )

    def test_coordinate_atoms_are_rejected_from_base_inputs(self) -> None:
        bad_atoms = set(self.system.branches["A_rec"])
        bad_atoms.add("qrgs")
        with self.assertRaises(BranchBaseError):
            closure_projection(self.system, bad_atoms)


if __name__ == "__main__":
    unittest.main()
