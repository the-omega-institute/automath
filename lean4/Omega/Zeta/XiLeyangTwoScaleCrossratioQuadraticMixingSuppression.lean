import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.XiLeyangTwoScaleCrossratioSlopeExponent

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the two-scale Lee--Yang cross-ratio calculation with a quadratic
mixing perturbation.  The affine zero is the leading approximation; the quadratic zero is
the corrected zero. -/
structure XiLeyangTwoScaleCrossratioData where
  L : ℝ
  y_h : ℝ
  omega : ℝ
  affineReference : ℝ
  affineZero : ℝ
  quadraticZero : ℝ
  crossratioLipschitz : ℝ
  invariantCorrection : ℝ
  hL_pos : 0 < L
  crossratioLipschitz_nonneg : 0 ≤ crossratioLipschitz
  affineLeadingApproximation : ℝ
  affineLeadingApproximation_eq :
    affineZero = affineReference + affineLeadingApproximation * L ^ (-y_h)
  quadraticPerturbation_bound :
    |quadraticZero - affineZero| ≤ L ^ (-2 * y_h)
  crossratioLipschitz_estimate :
    |xiLeyangTwoScaleCrossratio affineReference quadraticZero -
        xiLeyangTwoScaleCrossratio affineReference affineZero| ≤
      crossratioLipschitz * L ^ y_h * |quadraticZero - affineZero|
  invariantCorrection_bound :
    |invariantCorrection| ≤ L ^ (-omega)

namespace XiLeyangTwoScaleCrossratioData

/-- The cross-ratio defect caused only by replacing the affine zero with the quadratic zero. -/
def xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_crossratioDefect
    (D : XiLeyangTwoScaleCrossratioData) : ℝ :=
  xiLeyangTwoScaleCrossratio D.affineReference D.quadraticZero -
    xiLeyangTwoScaleCrossratio D.affineReference D.affineZero

/-- The final paper-facing estimate: the affine leading term is recorded, the inverse correction
is second order in the magnetic scale, the cross-ratio defect is suppressed by `L^{-y_h}`, and the
already-present invariant correction stays at its independent exponent. -/
def quadraticMixingSuppression (D : XiLeyangTwoScaleCrossratioData) : Prop :=
  D.affineZero =
      D.affineReference + D.affineLeadingApproximation * D.L ^ (-D.y_h) ∧
    |D.quadraticZero - D.affineZero| ≤ D.L ^ (-2 * D.y_h) ∧
    |D.xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_crossratioDefect| ≤
      D.crossratioLipschitz * D.L ^ (-D.y_h) ∧
    |D.invariantCorrection| ≤ D.L ^ (-D.omega)

lemma xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_scale
    (D : XiLeyangTwoScaleCrossratioData) :
    D.L ^ D.y_h * D.L ^ (-2 * D.y_h) = D.L ^ (-D.y_h) := by
  rw [← Real.rpow_add D.hL_pos]
  ring_nf

lemma xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_crossratio_bound
    (D : XiLeyangTwoScaleCrossratioData) :
    |D.xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_crossratioDefect| ≤
      D.crossratioLipschitz * D.L ^ (-D.y_h) := by
  calc
    |D.xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_crossratioDefect| =
        |xiLeyangTwoScaleCrossratio D.affineReference D.quadraticZero -
          xiLeyangTwoScaleCrossratio D.affineReference D.affineZero| := by
          rfl
    _ ≤ D.crossratioLipschitz * D.L ^ D.y_h *
        |D.quadraticZero - D.affineZero| := D.crossratioLipschitz_estimate
    _ ≤ D.crossratioLipschitz * D.L ^ D.y_h * D.L ^ (-2 * D.y_h) := by
          gcongr
          exact mul_nonneg D.crossratioLipschitz_nonneg
            (Real.rpow_nonneg D.hL_pos.le D.y_h)
          exact D.quadraticPerturbation_bound
    _ = D.crossratioLipschitz * D.L ^ (-D.y_h) := by
          rw [mul_assoc,
            D.xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_scale]

end XiLeyangTwoScaleCrossratioData

open XiLeyangTwoScaleCrossratioData

/-- Paper label: `prop:xi-leyang-two-scale-crossratio-quadratic-mixing-suppression`. -/
theorem paper_xi_leyang_two_scale_crossratio_quadratic_mixing_suppression
    (D : XiLeyangTwoScaleCrossratioData) : D.quadraticMixingSuppression := by
  exact ⟨D.affineLeadingApproximation_eq, D.quadraticPerturbation_bound,
    D.xi_leyang_two_scale_crossratio_quadratic_mixing_suppression_crossratio_bound,
    D.invariantCorrection_bound⟩

end

end Omega.Zeta
