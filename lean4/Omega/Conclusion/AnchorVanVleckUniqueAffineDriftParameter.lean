import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanVanVleckCoeffResidueBilinearLock

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete Van Vleck coefficient package for the unique affine drift parameter.  The residue
moments are the same finite sums used in the basepoint-scan coefficient lock, and the affine drift
parameter is the real centroid `∑ γ_k`. -/
structure conclusion_anchor_vanvleck_unique_affine_drift_parameter_data where
  kappa : ℕ
  pole : Fin kappa → ℂ
  residue : Fin kappa → ℂ
  gamma : Fin kappa → ℝ
  A1 : ℝ
  b0 : ℝ
  b1 : ℝ
  leadingCoefficientExpansion : b0 = -((kappa : ℝ) * (kappa + 1))
  centroidExpansion : A1 = -2 * ∑ k, gamma k
  firstResidueMoment :
    2 * ∑ k, Complex.re (pole k * residue k) = -((kappa : ℝ) * (kappa + 1))
  secondResidueMoment :
    2 * ∑ k, Complex.re ((pole k) ^ 2 * residue k) = b1 - b0 * A1

namespace conclusion_anchor_vanvleck_unique_affine_drift_parameter_data

/-- The leading Van Vleck coefficient is the residue moment invariant. -/
def leading_coeff_invariant
    (D : conclusion_anchor_vanvleck_unique_affine_drift_parameter_data) : Prop :=
  D.b0 = 2 * ∑ k, Complex.re (D.pole k * D.residue k)

/-- The coefficient `b₁` has the unique affine drift controlled by `∑ γ_k`. -/
def affine_drift_law
    (D : conclusion_anchor_vanvleck_unique_affine_drift_parameter_data) : Prop :=
  D.b1 =
    2 * ∑ k, Complex.re ((D.pole k) ^ 2 * D.residue k) +
      2 * (D.kappa : ℝ) * (D.kappa + 1) * ∑ k, D.gamma k

/-- After subtracting the affine drift, the translated invariant `I(p)` is the second residue
moment and no longer depends on the centroid translation. -/
def translation_invariant
    (D : conclusion_anchor_vanvleck_unique_affine_drift_parameter_data) : Prop :=
  D.b1 - 2 * (D.kappa : ℝ) * (D.kappa + 1) * ∑ k, D.gamma k =
    2 * ∑ k, Complex.re ((D.pole k) ^ 2 * D.residue k)

end conclusion_anchor_vanvleck_unique_affine_drift_parameter_data

/-- Paper label: `thm:conclusion-anchor-vanvleck-unique-affine-drift-parameter`. -/
theorem paper_conclusion_anchor_vanvleck_unique_affine_drift_parameter
    (D : conclusion_anchor_vanvleck_unique_affine_drift_parameter_data) :
    D.leading_coeff_invariant ∧ D.affine_drift_law ∧ D.translation_invariant := by
  have h :=
    Omega.Zeta.paper_xi_basepoint_scan_van_vleck_coeff_residue_bilinear_lock
      D.kappa D.pole D.residue D.gamma D.A1 D.b0 D.b1
      D.leadingCoefficientExpansion D.centroidExpansion D.firstResidueMoment
      D.secondResidueMoment
  refine ⟨h.1, h.2.2, ?_⟩
  unfold conclusion_anchor_vanvleck_unique_affine_drift_parameter_data.translation_invariant
  rw [h.2.2]
  ring

end Omega.Conclusion
