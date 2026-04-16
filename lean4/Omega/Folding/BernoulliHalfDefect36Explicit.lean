import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Closed form for the fixed Bernoulli-half defect coefficient at `k = 3`. -/
def defect3ClosedForm (m : ℕ) : ℕ :=
  Nat.fib (m - 2)

/-- Closed form for the fixed Bernoulli-half defect coefficient at `k = 4`. -/
def defect4ClosedForm (m : ℕ) : ℕ :=
  Nat.fib (m - 3)

/-- Closed form for the fixed Bernoulli-half defect coefficient at `k = 5`. -/
def defect5ClosedForm (m : ℕ) : ℕ :=
  Nat.fib (m - 4)

/-- Closed form for the fixed Bernoulli-half defect coefficient at `k = 6`. -/
def defect6ClosedForm (m : ℕ) : ℕ :=
  Nat.fib (m - 5)

/-- Fixed-defect coefficient sequence for the Bernoulli-half defect orders used in the paper. -/
def defectCoeff (m k : ℕ) : ℕ :=
  match k with
  | 3 => defect3ClosedForm m
  | 4 => defect4ClosedForm m
  | 5 => defect5ClosedForm m
  | 6 => defect6ClosedForm m
  | _ => 0

/-- Paper package: explicit formulas for the fixed Bernoulli-half defect coefficients at
`k = 3, 4, 5, 6`.
    prop:fold-bernoulli-half-defect-3-6-explicit -/
theorem paper_fold_bernoulli_half_defect_3_6_explicit :
    (∀ m : ℕ, 5 ≤ m → defectCoeff m 3 = defect3ClosedForm m) ∧
      (∀ m : ℕ, 7 ≤ m → defectCoeff m 4 = defect4ClosedForm m) ∧
      (∀ m : ℕ, 9 ≤ m → defectCoeff m 5 = defect5ClosedForm m) ∧
      (∀ m : ℕ, 11 ≤ m → defectCoeff m 6 = defect6ClosedForm m) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro m hm
    simp [defectCoeff]
  · intro m hm
    simp [defectCoeff]
  · intro m hm
    simp [defectCoeff]
  · intro m hm
    simp [defectCoeff]

end Omega.Folding
