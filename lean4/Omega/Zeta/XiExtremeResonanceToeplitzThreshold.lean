import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.UnitCirclePhaseArithmetic.AppHorizonToeplitzDetectionThreshold

namespace Omega.Zeta

/-- Concrete pole/remainder package for the extreme-resonance Toeplitz threshold. The audited
pole mass plus the audited remainder reconstructs the resonance quality factor `Qᵨ`, and the
appendix Toeplitz threshold applies to that explicit value. -/
structure xi_extreme_resonance_toeplitz_threshold_data where
  xi_extreme_resonance_toeplitz_threshold_N : ℝ
  xi_extreme_resonance_toeplitz_threshold_C : ℝ
  xi_extreme_resonance_toeplitz_threshold_δ : ℝ
  xi_extreme_resonance_toeplitz_threshold_poleMass : ℝ
  xi_extreme_resonance_toeplitz_threshold_auditedRemainder : ℝ
  xi_extreme_resonance_toeplitz_threshold_Qrho : ℝ
  xi_extreme_resonance_toeplitz_threshold_C_pos :
    0 < xi_extreme_resonance_toeplitz_threshold_C
  xi_extreme_resonance_toeplitz_threshold_Qrho_eq :
    xi_extreme_resonance_toeplitz_threshold_Qrho =
      xi_extreme_resonance_toeplitz_threshold_poleMass +
        xi_extreme_resonance_toeplitz_threshold_auditedRemainder
  xi_extreme_resonance_toeplitz_threshold_auditedToeplitzBound :
    (xi_extreme_resonance_toeplitz_threshold_poleMass +
        xi_extreme_resonance_toeplitz_threshold_auditedRemainder) *
        Real.log
          (1 + xi_extreme_resonance_toeplitz_threshold_δ *
            (xi_extreme_resonance_toeplitz_threshold_poleMass +
              xi_extreme_resonance_toeplitz_threshold_auditedRemainder)) ≤
      xi_extreme_resonance_toeplitz_threshold_C *
        xi_extreme_resonance_toeplitz_threshold_N

/-- The explicit resonance threshold obtained after rewriting the appendix Toeplitz quality factor
in terms of the audited pole-plus-remainder package. -/
def xi_extreme_resonance_toeplitz_threshold_statement
    (D : xi_extreme_resonance_toeplitz_threshold_data) : Prop :=
  D.xi_extreme_resonance_toeplitz_threshold_C⁻¹ *
      D.xi_extreme_resonance_toeplitz_threshold_Qrho *
      Real.log
        (1 + D.xi_extreme_resonance_toeplitz_threshold_δ *
          D.xi_extreme_resonance_toeplitz_threshold_Qrho) ≤
    D.xi_extreme_resonance_toeplitz_threshold_N

/-- Paper label: `prop:xi-extreme-resonance-toeplitz-threshold`. Rewriting the resonance quality
factor `Qᵨ` using the audited pole data and remainder term puts the statement exactly in the form
of the appendix horizon Toeplitz detection threshold. -/
theorem paper_xi_extreme_resonance_toeplitz_threshold
    (D : xi_extreme_resonance_toeplitz_threshold_data) :
    xi_extreme_resonance_toeplitz_threshold_statement D := by
  let D0 : Omega.UnitCirclePhaseArithmetic.HorizonToeplitzDetectionData :=
    { N := D.xi_extreme_resonance_toeplitz_threshold_N
      C := D.xi_extreme_resonance_toeplitz_threshold_C
      δ := D.xi_extreme_resonance_toeplitz_threshold_δ
      Qrho := D.xi_extreme_resonance_toeplitz_threshold_Qrho
      C_pos := D.xi_extreme_resonance_toeplitz_threshold_C_pos }
  have hToeplitz : D0.toeplitzPsdUpToN := by
    simpa [D0, Omega.UnitCirclePhaseArithmetic.HorizonToeplitzDetectionData.toeplitzPsdUpToN,
      D.xi_extreme_resonance_toeplitz_threshold_Qrho_eq] using
      D.xi_extreme_resonance_toeplitz_threshold_auditedToeplitzBound
  simpa [xi_extreme_resonance_toeplitz_threshold_statement, D0] using
    Omega.UnitCirclePhaseArithmetic.paper_app_horizon_toeplitz_detection_threshold D0 hToeplitz

end Omega.Zeta
