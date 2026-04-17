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

/-- Paper-facing relative-scale transfer package for finite-part `log M`: the explicit truncation
bound controls the finite tail, and after dividing by `|logM|` the same control transfers to the
relative scale whenever `logM ≠ 0`.
    cor:finite-part-logM-relative-scale-transfer -/
def paper_finite_part_logM_relative_scale_transfer
    (d K L : ℕ) (lam logMK logML logM : ℝ) : Prop := by
  let _ := d
  let _ := K
  let _ := L
  exact
    ((0 ≤ lam ∧ lam < 1) →
      finitePartLogMRelativeTailBound lam ≤ lam ^ 2 / (1 - lam)) ∧
      ((0 ≤ lam ∧ lam < 1 ∧ logM ≠ 0 ∧
          finitePartLogMRelativeGap logMK logML ≤ finitePartLogMRelativeTailBound lam) →
        finitePartLogMRelativeScale logMK logML logM ≤ (lam ^ 2 / (1 - lam)) / |logM|)

theorem paper_finite_part_logM_relative_scale_transfer_spec
    (d K L : ℕ) (lam logMK logML logM : ℝ) :
    paper_finite_part_logM_relative_scale_transfer d K L lam logMK logML logM := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h0, h1⟩
    exact finitePartLogMRelativeTailBound_le lam h0 h1
  · rintro ⟨h0, h1, hlogM, hgap⟩
    exact finitePartLogMRelativeScaleTransfer_le lam logMK logML logM h0 h1 hgap hlogM

end Omega.Zeta
