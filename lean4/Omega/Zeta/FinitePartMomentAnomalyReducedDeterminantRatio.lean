import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:finite-part-moment-anomaly-reduced-determinant-ratio`. Rewriting the
residue constants as inverse reduced determinants turns the anomaly into a direct logarithmic
subtraction, after which the inverse signs simplify by `log_inv`. -/
theorem paper_finite_part_moment_anomaly_reduced_determinant_ratio
    (q : ℕ) (hq : 2 ≤ q) (C1 Cq det1 detq : ℝ) (hC1 : C1 = det1⁻¹) (hCq : Cq = detq⁻¹) :
    Real.log Cq - (q : ℝ) * Real.log C1 = -Real.log detq + (q : ℝ) * Real.log det1 := by
  have paper_finite_part_moment_anomaly_reduced_determinant_ratio_q_nonneg :
      (0 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast le_trans (show 0 ≤ 2 by decide) hq
  subst C1 Cq
  rw [Real.log_inv, Real.log_inv]
  linarith

end Omega.Zeta
