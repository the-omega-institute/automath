import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.PsiTruncationBounds

namespace Omega.Zeta

open Real
open Omega.Zeta.PsiTruncationBounds

/-- The finite-part log-gap between two truncation scales. -/
noncomputable def finitePartLogMRelativeGap (logMK logML : ℝ) : ℝ :=
  |logMK - logML|

/-- The relative-scale transfer normalizes the finite-part gap by `|logM|`. -/
noncomputable def finitePartLogMRelativeScale (logMK logML logM : ℝ) : ℝ :=
  finitePartLogMRelativeGap logMK logML / |logM|

/-- The explicit finite-tail majorant coming from the already verified truncation bound. -/
noncomputable def finitePartLogMRelativeTailBound (lam : ℝ) : ℝ :=
  psi lam

theorem finitePartLogMRelativeTailBound_le
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    finitePartLogMRelativeTailBound lam ≤ lam ^ 2 / (1 - lam) := by
  exact paper_finite_part_gap_truncation_bounds lam h0 h1

theorem finitePartLogMRelativeScaleTransfer_le
    (lam logMK logML logM : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam < 1)
    (hgap : finitePartLogMRelativeGap logMK logML ≤ finitePartLogMRelativeTailBound lam)
    (hlogM : logM ≠ 0) :
    finitePartLogMRelativeScale logMK logML logM ≤ (lam ^ 2 / (1 - lam)) / |logM| := by
  have htail : finitePartLogMRelativeTailBound lam ≤ lam ^ 2 / (1 - lam) :=
    finitePartLogMRelativeTailBound_le lam h0 h1
  have hInvNonneg : 0 ≤ |logM|⁻¹ := by positivity
  have hdiv :
      finitePartLogMRelativeGap logMK logML * |logM|⁻¹
        ≤ finitePartLogMRelativeTailBound lam * |logM|⁻¹ :=
    mul_le_mul_of_nonneg_right hgap hInvNonneg
  have htail_div :
      finitePartLogMRelativeTailBound lam * |logM|⁻¹
        ≤ (lam ^ 2 / (1 - lam)) * |logM|⁻¹ :=
    mul_le_mul_of_nonneg_right htail hInvNonneg
  simpa [finitePartLogMRelativeScale, div_eq_mul_inv] using le_trans hdiv htail_div

/-- Paper-facing relative-scale transfer package for finite-part `log M`.
    cor:finite-part-logM-relative-scale-transfer -/
theorem paper_finite_part_logm_relative_scale_transfer {logM logMK logML B : Real}
    (hKL : |logML - logMK| ≤ B) (hKM : |logMK - logM| ≤ B) (hlogM : logM ≠ 0) :
    |logML - logMK| ≤ B ∧ |logMK / logM - 1| ≤ B / |logM| := by
  refine ⟨hKL, ?_⟩
  have hrewrite : logMK / logM - 1 = (logMK - logM) / logM := by
    field_simp [hlogM]
  calc
    |logMK / logM - 1| = |(logMK - logM) / logM| := by rw [hrewrite]
    _ = |logMK - logM| / |logM| := by rw [abs_div]
    _ ≤ B / |logM| := by
      exact div_le_div_of_nonneg_right hKM (abs_nonneg logM)

end Omega.Zeta
