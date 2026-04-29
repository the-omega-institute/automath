import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete two-step saturation data for the golden residual calculation.  The first saturation
identifies the numerator with `|μ_q|`, the second identifies the denominator with `r_q`; the
Aitken residual limit and the complex-gap limit are then transported to the paper-facing
normalizations. -/
structure conclusion_kernel_rh_golden_residual_two_step_saturation_data where
  conclusion_kernel_rh_golden_residual_two_step_saturation_mu : ℕ → ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_r : ℕ → ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_eta : ℕ → ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_R : ℕ → ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_g : ℕ → ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_goldenResidual : ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_complexGapConstant : ℝ
  conclusion_kernel_rh_golden_residual_two_step_saturation_firstSaturation :
    ∀ q,
      conclusion_kernel_rh_golden_residual_two_step_saturation_eta q =
        |conclusion_kernel_rh_golden_residual_two_step_saturation_mu q|
  conclusion_kernel_rh_golden_residual_two_step_saturation_secondSaturation :
    ∀ q,
      conclusion_kernel_rh_golden_residual_two_step_saturation_R q =
        conclusion_kernel_rh_golden_residual_two_step_saturation_r q
  conclusion_kernel_rh_golden_residual_two_step_saturation_aitkenResidualLimit :
    Tendsto
      (fun q : ℕ =>
        conclusion_kernel_rh_golden_residual_two_step_saturation_eta q /
          conclusion_kernel_rh_golden_residual_two_step_saturation_R q)
      atTop
      (nhds conclusion_kernel_rh_golden_residual_two_step_saturation_goldenResidual)
  conclusion_kernel_rh_golden_residual_two_step_saturation_gapLimitConsequence :
    Tendsto
      (fun q : ℕ =>
        (q : ℝ) * conclusion_kernel_rh_golden_residual_two_step_saturation_g q)
      atTop
      (nhds conclusion_kernel_rh_golden_residual_two_step_saturation_complexGapConstant)

/-- The normalized residual has the supplied golden residual limit. -/
def conclusion_kernel_rh_golden_residual_two_step_saturation_data.residualLimit
    (D : conclusion_kernel_rh_golden_residual_two_step_saturation_data) : Prop :=
  Tendsto
    (fun q : ℕ =>
      |D.conclusion_kernel_rh_golden_residual_two_step_saturation_mu q| /
        D.conclusion_kernel_rh_golden_residual_two_step_saturation_r q)
    atTop
    (nhds D.conclusion_kernel_rh_golden_residual_two_step_saturation_goldenResidual)

/-- The complex gap has the supplied `q * g_q` limit. -/
def conclusion_kernel_rh_golden_residual_two_step_saturation_data.complexGapLimit
    (D : conclusion_kernel_rh_golden_residual_two_step_saturation_data) : Prop :=
  Tendsto
    (fun q : ℕ =>
      (q : ℝ) * D.conclusion_kernel_rh_golden_residual_two_step_saturation_g q)
    atTop
    (nhds D.conclusion_kernel_rh_golden_residual_two_step_saturation_complexGapConstant)

/-- Paper label: `thm:conclusion-kernel-rh-golden-residual-two-step-saturation`. -/
theorem paper_conclusion_kernel_rh_golden_residual_two_step_saturation
    (D : conclusion_kernel_rh_golden_residual_two_step_saturation_data) :
    D.residualLimit ∧ D.complexGapLimit := by
  have hquot :
      (fun q : ℕ =>
        |D.conclusion_kernel_rh_golden_residual_two_step_saturation_mu q| /
          D.conclusion_kernel_rh_golden_residual_two_step_saturation_r q) =
        (fun q : ℕ =>
          D.conclusion_kernel_rh_golden_residual_two_step_saturation_eta q /
            D.conclusion_kernel_rh_golden_residual_two_step_saturation_R q) := by
    funext q
    rw [← D.conclusion_kernel_rh_golden_residual_two_step_saturation_firstSaturation q,
      ← D.conclusion_kernel_rh_golden_residual_two_step_saturation_secondSaturation q]
  exact ⟨by
    simpa [conclusion_kernel_rh_golden_residual_two_step_saturation_data.residualLimit, hquot]
      using
        D.conclusion_kernel_rh_golden_residual_two_step_saturation_aitkenResidualLimit,
    D.conclusion_kernel_rh_golden_residual_two_step_saturation_gapLimitConsequence⟩

end Omega.Conclusion
