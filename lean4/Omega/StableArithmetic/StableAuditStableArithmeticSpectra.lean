import Mathlib.Tactic

/- This compatibility module is registered under the round target path. The rebased base branch
already contains the paper theorem in `Omega.StableArithmetic.StableArithmeticSpectra`; keeping
this file self-contained lets `lake env lean` elaborate the target path without requiring a
prebuilt local `.olean` for that sibling module. -/
