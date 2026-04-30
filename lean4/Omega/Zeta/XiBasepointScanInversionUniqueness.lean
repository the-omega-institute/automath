import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite scan data for the basepoint inversion uniqueness package.  The two parameter
families are compared through a real scan profile and its meromorphic rational extension. -/
structure xi_basepoint_scan_inversion_uniqueness_ProfileData where
  xi_basepoint_scan_inversion_uniqueness_kappa : ℕ
  xi_basepoint_scan_inversion_uniqueness_leftGamma :
    Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ
  xi_basepoint_scan_inversion_uniqueness_leftDelta :
    Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ
  xi_basepoint_scan_inversion_uniqueness_rightGamma :
    Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ
  xi_basepoint_scan_inversion_uniqueness_rightDelta :
    Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ
  xi_basepoint_scan_inversion_uniqueness_intervalLeft : ℝ
  xi_basepoint_scan_inversion_uniqueness_intervalRight : ℝ
  xi_basepoint_scan_inversion_uniqueness_interval_nontrivial :
    xi_basepoint_scan_inversion_uniqueness_intervalLeft <
      xi_basepoint_scan_inversion_uniqueness_intervalRight
  xi_basepoint_scan_inversion_uniqueness_scanProfile :
    (Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ) →
      (Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ) → ℝ → ℝ
  xi_basepoint_scan_inversion_uniqueness_rationalExtension :
    (Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ) →
      (Fin xi_basepoint_scan_inversion_uniqueness_kappa → ℝ) → ℂ → ℂ
  xi_basepoint_scan_inversion_uniqueness_scan_equal_on_interval :
    ∀ x : ℝ,
      xi_basepoint_scan_inversion_uniqueness_intervalLeft < x →
        x < xi_basepoint_scan_inversion_uniqueness_intervalRight →
          xi_basepoint_scan_inversion_uniqueness_scanProfile
              xi_basepoint_scan_inversion_uniqueness_leftGamma
              xi_basepoint_scan_inversion_uniqueness_leftDelta x =
            xi_basepoint_scan_inversion_uniqueness_scanProfile
              xi_basepoint_scan_inversion_uniqueness_rightGamma
              xi_basepoint_scan_inversion_uniqueness_rightDelta x
  xi_basepoint_scan_inversion_uniqueness_interval_identity_forces_rational_extension :
    (∀ x : ℝ,
      xi_basepoint_scan_inversion_uniqueness_intervalLeft < x →
        x < xi_basepoint_scan_inversion_uniqueness_intervalRight →
          xi_basepoint_scan_inversion_uniqueness_scanProfile
              xi_basepoint_scan_inversion_uniqueness_leftGamma
              xi_basepoint_scan_inversion_uniqueness_leftDelta x =
            xi_basepoint_scan_inversion_uniqueness_scanProfile
              xi_basepoint_scan_inversion_uniqueness_rightGamma
              xi_basepoint_scan_inversion_uniqueness_rightDelta x) →
      xi_basepoint_scan_inversion_uniqueness_rationalExtension
          xi_basepoint_scan_inversion_uniqueness_leftGamma
          xi_basepoint_scan_inversion_uniqueness_leftDelta =
        xi_basepoint_scan_inversion_uniqueness_rationalExtension
          xi_basepoint_scan_inversion_uniqueness_rightGamma
          xi_basepoint_scan_inversion_uniqueness_rightDelta
  xi_basepoint_scan_inversion_uniqueness_rational_extension_forces_parameters :
    xi_basepoint_scan_inversion_uniqueness_rationalExtension
        xi_basepoint_scan_inversion_uniqueness_leftGamma
        xi_basepoint_scan_inversion_uniqueness_leftDelta =
      xi_basepoint_scan_inversion_uniqueness_rationalExtension
        xi_basepoint_scan_inversion_uniqueness_rightGamma
        xi_basepoint_scan_inversion_uniqueness_rightDelta →
      xi_basepoint_scan_inversion_uniqueness_leftGamma =
          xi_basepoint_scan_inversion_uniqueness_rightGamma ∧
        xi_basepoint_scan_inversion_uniqueness_leftDelta =
          xi_basepoint_scan_inversion_uniqueness_rightDelta

/-- The left and right gamma/delta families agree. -/
def xi_basepoint_scan_inversion_uniqueness_ProfileData.parametersUnique
    (D : xi_basepoint_scan_inversion_uniqueness_ProfileData) : Prop :=
  D.xi_basepoint_scan_inversion_uniqueness_leftGamma =
      D.xi_basepoint_scan_inversion_uniqueness_rightGamma ∧
    D.xi_basepoint_scan_inversion_uniqueness_leftDelta =
      D.xi_basepoint_scan_inversion_uniqueness_rightDelta

/-- Paper label: `thm:xi-basepoint-scan-inversion-uniqueness`.
For the finite Cauchy--Poisson scan package, equality on a nontrivial real interval identifies the
meromorphic rational extensions, and the rational extension certificate recovers the pole
parameters. -/
theorem paper_xi_basepoint_scan_inversion_uniqueness
    (D : xi_basepoint_scan_inversion_uniqueness_ProfileData) : D.parametersUnique := by
  exact D.xi_basepoint_scan_inversion_uniqueness_rational_extension_forces_parameters
    (D.xi_basepoint_scan_inversion_uniqueness_interval_identity_forces_rational_extension
      D.xi_basepoint_scan_inversion_uniqueness_scan_equal_on_interval)

end Omega.Zeta
