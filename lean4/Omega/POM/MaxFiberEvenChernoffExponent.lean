import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.GoldenCouplingUniqueness

namespace Omega.POM

open scoped goldenRatio

private theorem bernoulli_bhattacharyya_midpoint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * Real.sqrt (p * (1 - p)) ≤ 1 := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hsq :
      2 * (Real.sqrt p * Real.sqrt (1 - p)) ≤ p + (1 - p) := by
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt (1 - p)), Real.sq_sqrt hp0, Real.sq_sqrt hq0]
  have hmul : Real.sqrt (p * (1 - p)) = Real.sqrt p * Real.sqrt (1 - p) := by
    rw [Real.sqrt_mul hp0]
  calc
    2 * Real.sqrt (p * (1 - p)) = 2 * (Real.sqrt p * Real.sqrt (1 - p)) := by
      rw [hmul]
    _ ≤ p + (1 - p) := hsq
    _ = 1 := by ring

/-- Paper: `thm:pom-max-fiber-even-chernoff-exponent`.
    The symmetric Bernoulli pair is controlled by the midpoint Bhattacharyya coefficient, and the
    golden stable limit simplifies via the standard golden-ratio identities. -/
theorem paper_pom_max_fiber_even_chernoff_exponent :
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 → 2 * Real.sqrt (p * (1 - p)) ≤ 1) ∧
    ((Real.goldenRatio - Real.goldenRatio⁻¹) / 2 = 1 / 2) ∧
    (((Real.goldenRatio - Real.goldenRatio⁻¹) / 2) ^ 2 = 1 / 4) := by
  exact ⟨bernoulli_bhattacharyya_midpoint, sinh_log_phi_eq_half, sinh_log_phi_sq⟩

end Omega.POM
