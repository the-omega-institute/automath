import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- If the scaled Pick--Poisson determinant is bounded by `δ²`, then the determinant itself
forces pseudohyperbolic separation at scale `δ`.
    cor:xi-pick-poisson-determinant-separation-sufficient -/
theorem paper_xi_pick_poisson_determinant_separation_sufficient (detP r δ : ℝ) (kappa : ℕ)
    (hdet : 0 ≤ detP) (hδ : 0 ≤ δ) (hr : 0 ≤ r ∧ r < 1)
    (hprod : detP * (1 - r) ^ (2 * kappa) ≤ δ ^ 2) :
    Real.sqrt detP * (1 - r) ^ kappa ≤ δ := by
  have hone_sub_nonneg : 0 ≤ 1 - r := sub_nonneg.mpr hr.2.le
  have hlhs_nonneg : 0 ≤ Real.sqrt detP * (1 - r) ^ kappa := by
    exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hone_sub_nonneg _)
  have hsq :
      (Real.sqrt detP * (1 - r) ^ kappa) ^ 2 ≤ δ ^ 2 := by
    calc
      (Real.sqrt detP * (1 - r) ^ kappa) ^ 2
          = (Real.sqrt detP) ^ 2 * ((1 - r) ^ kappa) ^ 2 := by rw [mul_pow]
      _ = detP * ((1 - r) ^ kappa) ^ 2 := by rw [Real.sq_sqrt hdet]
      _ = detP * (1 - r) ^ (2 * kappa) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ δ ^ 2 := hprod
  exact (sq_le_sq₀ hlhs_nonneg hδ).1 hsq

end Omega.Zeta
