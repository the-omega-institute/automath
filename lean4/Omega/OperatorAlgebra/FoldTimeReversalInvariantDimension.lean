import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- Fiberwise arithmetic form of the time-reversal invariant dimension count.
    cor:op-algebra-time-reversal-invariant-dimension -/
theorem paper_op_algebra_time_reversal_invariant_dimension {ι : Type*} [Fintype ι]
    (d fix : ι → ℕ) (hfix : ∀ x, fix x ≤ d x) (hparity : ∀ x, Even (d x - fix x)) :
    ∑ x, (((d x + fix x) / 2)^2 + ((d x - fix x) / 2)^2) =
      ∑ x, (d x ^ 2 + fix x ^ 2) / 2 := by
  classical
  refine Finset.sum_congr rfl ?_
  intro x hx
  rcases hparity x with ⟨k, hk⟩
  have hle := hfix x
  have hd : d x = fix x + 2 * k := by
    omega
  have hsum : (d x + fix x) / 2 = fix x + k := by
    rw [hd]
    calc
      (fix x + 2 * k + fix x) / 2 = (2 * (fix x + k)) / 2 := by
        ring_nf
      _ = fix x + k := by
        simp
  have hdiff : (d x - fix x) / 2 = k := by
    rw [hd]
    calc
      (fix x + 2 * k - fix x) / 2 = (2 * k) / 2 := by
        omega
      _ = k := by
        simp
  rw [hsum, hdiff, hd]
  have hdouble : (fix x + 2 * k) ^ 2 + fix x ^ 2 = 2 * ((fix x + k) ^ 2 + k ^ 2) := by
    ring
  calc
    (fix x + k) ^ 2 + k ^ 2 = (2 * ((fix x + k) ^ 2 + k ^ 2)) / 2 := by
      simp
    _ = ((fix x + 2 * k) ^ 2 + fix x ^ 2) / 2 := by
      rw [hdouble]

end Omega.OperatorAlgebra
