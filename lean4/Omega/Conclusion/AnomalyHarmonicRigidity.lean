import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Omega.Conclusion.AnomalyHarmonicRigidity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pythagorean identity for addition when the inner product vanishes.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem norm_add_sq_of_inner_zero (h r : V) (hperp : inner ℝ h r = (0 : ℝ)) :
    ‖h + r‖^2 = ‖h‖^2 + ‖r‖^2 := by
  have hform := norm_add_sq_real h r
  linarith [hperp, hform]

/-- Pythagorean identity for subtraction when the inner product vanishes.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem norm_sub_sq_of_inner_zero (h r : V) (hperp : inner ℝ h r = (0 : ℝ)) :
    ‖h - r‖^2 = ‖h‖^2 + ‖r‖^2 := by
  have hform := norm_sub_sq_real h r
  linarith [hperp, hform]

/-- Anomaly Pythagoras: `‖(p+h)-q‖² = ‖h‖² + ‖r‖²` when `q = p+r` and `⟨h,r⟩ = 0`.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem anomaly_pythagoras (p h q r : V)
    (ha : q = p + r) (hperp : inner ℝ h r = (0 : ℝ)) :
    ‖(p + h) - q‖^2 = ‖h‖^2 + ‖r‖^2 := by
  have hstep : (p + h) - q = h - r := by
    rw [ha]; abel
  rw [hstep]
  exact norm_sub_sq_of_inner_zero h r hperp

omit [InnerProductSpace ℝ V] in
/-- Residual at exact match: `‖(p+h)-p‖² = ‖h‖²`.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem min_residual_eq_h_norm_sq (p h : V) :
    ‖(p + h) - p‖^2 = ‖h‖^2 := by
  have : (p + h) - p = h := by abel
  rw [this]

omit [InnerProductSpace ℝ V] in
/-- Strict equality iff anomaly vector is zero.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem strictify_iff_h_zero (p h : V) : (p + h = p) ↔ (h = 0) := by
  constructor
  · intro hh
    have : p + h = p + 0 := by rw [add_zero]; exact hh
    exact add_left_cancel this
  · intro hh
    rw [hh, add_zero]

/-- Packaged min-residual form.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem min_residual_anomaly (p h q r : V)
    (ha : q = p + r) (hperp : inner ℝ h r = (0 : ℝ)) :
    ‖(p + h) - q‖^2 = ‖h‖^2 + ‖r‖^2 :=
  anomaly_pythagoras p h q r ha hperp

/-- Paper package: anomaly harmonic rigidity.
    thm:conclusion-anomaly-harmonic-rigidity -/
theorem paper_conclusion_anomaly_harmonic_rigidity
    (p h q r : V) (ha : q = p + r) (hperp : inner ℝ h r = (0 : ℝ)) :
    ‖(p + h) - q‖^2 = ‖h‖^2 + ‖r‖^2 :=
  anomaly_pythagoras p h q r ha hperp

end Omega.Conclusion.AnomalyHarmonicRigidity
