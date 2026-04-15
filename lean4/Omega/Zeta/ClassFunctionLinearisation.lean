import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for class-function determinant linearisation in
    the ETDS Chebotarev section.
    thm:class-function-linearisation -/
theorem paper_etds_class_function_linearisation
    {Irr : Type}
    [Fintype Irr]
    [DecidableEq Irr]
    (classLogarithm : ℂ)
    (fourierCoeff traceLog determinantLog : Irr → ℂ)
    (hExpand :
      classLogarithm = ∑ ρ, fourierCoeff ρ * traceLog ρ)
    (hDet : ∀ ρ, traceLog ρ = determinantLog ρ) :
    classLogarithm = ∑ ρ, fourierCoeff ρ * determinantLog ρ := by
  calc
    classLogarithm = ∑ ρ, fourierCoeff ρ * traceLog ρ := hExpand
    _ = ∑ ρ, fourierCoeff ρ * determinantLog ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hDet ρ]

end Omega.Zeta
