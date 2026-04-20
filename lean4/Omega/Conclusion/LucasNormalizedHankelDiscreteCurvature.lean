import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.LucasBarrier

namespace Omega.Conclusion

open scoped BigOperators
open Omega.Zeta.LucasBarrier

/-- The normalized Lucas Hankel minor given by the closed product formula. -/
def lucasNormalizedHankelMinor (n k : ℕ) : ℕ :=
  Finset.prod (Finset.range k) fun i => lucas (n + i + 1)

@[simp] theorem lucasNormalizedHankelMinor_zero (n : ℕ) :
    lucasNormalizedHankelMinor n 0 = 1 := by
  simp [lucasNormalizedHankelMinor]

@[simp] theorem lucasNormalizedHankelMinor_succ (n k : ℕ) :
    lucasNormalizedHankelMinor n (k + 1) =
      lucasNormalizedHankelMinor n k * lucas (n + k + 1) := by
  simp [lucasNormalizedHankelMinor, Finset.prod_range_succ]

theorem lucasNormalizedHankelMinor_shift_ratio (n k : ℕ) :
    lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) k =
      lucasNormalizedHankelMinor n k * lucas (n + k + 1) := by
  induction k with
  | zero =>
      simp [lucasNormalizedHankelMinor]
  | succ k ih =>
      calc
        lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) (k + 1)
            = (lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) k) *
                lucas (n + k + 2) := by
                  rw [lucasNormalizedHankelMinor_succ]
                  ac_rfl
        _ = (lucasNormalizedHankelMinor n k * lucas (n + k + 1)) * lucas (n + k + 2) := by
              rw [ih]
        _ = lucasNormalizedHankelMinor n (k + 1) * lucas (n + k + 2) := by
              rw [lucasNormalizedHankelMinor_succ]

theorem lucasNormalizedHankelMinor_discrete_curvature (n k : ℕ) :
    lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) k =
      lucasNormalizedHankelMinor n (k + 1) := by
  rw [lucasNormalizedHankelMinor_succ, lucasNormalizedHankelMinor_shift_ratio]

/-- Proposition package for the normalized Lucas Hankel closed product formula and the
    two discrete-curvature ratio identities.
    thm:conclusion-lucas-normalized-hankel-discrete-curvature -/
def paper_conclusion_lucas_normalized_hankel_discrete_curvature_statement : Prop :=
  ∀ n k : ℕ,
    lucasNormalizedHankelMinor n (k + 1) =
      lucasNormalizedHankelMinor n k * lucas (n + k + 1) ∧
    lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) k =
      lucasNormalizedHankelMinor n k * lucas (n + k + 1) ∧
    lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) k =
      lucasNormalizedHankelMinor n (k + 1)

theorem paper_conclusion_lucas_normalized_hankel_discrete_curvature :
    paper_conclusion_lucas_normalized_hankel_discrete_curvature_statement := by
  intro n k
  exact ⟨lucasNormalizedHankelMinor_succ n k, lucasNormalizedHankelMinor_shift_ratio n k,
    lucasNormalizedHankelMinor_discrete_curvature n k⟩

end Omega.Conclusion
