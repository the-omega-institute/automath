import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Omega.Zeta.ClassFunctionLinearisation

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for Adams-Mobius primitive inversion in the
    ETDS Chebotarev section.
    cor:class-function-adams-mobius -/
theorem paper_etds_class_function_adams_mobius
    {Irr Adams : Type}
    [Fintype Irr]
    [DecidableEq Irr]
    [Fintype Adams]
    [DecidableEq Adams]
    (primitiveSeries : ℂ)
    (adamsClassLog adamsDeterminantLog : Adams → ℂ)
    (fourierCoeff : Adams → Irr → ℂ)
    (traceLog determinantLog : Adams → Irr → ℂ)
    (hPrimitive : primitiveSeries = ∑ m, adamsClassLog m)
    (hExpand : ∀ m, adamsClassLog m = ∑ ρ, fourierCoeff m ρ * traceLog m ρ)
    (hDet : ∀ m ρ, traceLog m ρ = determinantLog m ρ)
    (hDetLog : ∀ m, adamsDeterminantLog m = ∑ ρ, fourierCoeff m ρ * determinantLog m ρ) :
    primitiveSeries = ∑ m, adamsDeterminantLog m := by
  calc
    primitiveSeries = ∑ m, adamsClassLog m := hPrimitive
    _ = ∑ m, ∑ ρ, fourierCoeff m ρ * determinantLog m ρ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact
        paper_etds_class_function_linearisation
          (adamsClassLog m) (fourierCoeff m) (traceLog m) (determinantLog m)
          (hExpand m) (hDet m)
    _ = ∑ m, adamsDeterminantLog m := by
      symm
      apply Finset.sum_congr rfl
      intro m hm
      exact hDetLog m

end Omega.Zeta
