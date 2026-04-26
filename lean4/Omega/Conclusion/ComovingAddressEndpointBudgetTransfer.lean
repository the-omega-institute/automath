import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.Conclusion.ComovingEndpointAddressBudgetPhaseTransition
import Omega.TypedAddressBiaxialCompletion.ComovingBitBudget

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-comoving-address-endpoint-budget-transfer`. The fixed-chart
endpoint budget splits into the comoving endpoint cost plus an explicit address-prefix transfer
term, and removing that prefix restores the usual fixed-chart `2 log₂ T` lower bound. -/
theorem paper_conclusion_comoving_address_endpoint_budget_transfer
    (T delta : Real) (hT : 1 <= T) (hdelta : 0 < delta) :
    let pFix := Omega.TypedAddressBiaxialCompletion.typedAddressWorstCaseBitBudget T delta
    let pAddr := Real.logb 2 (((1 + delta)^2) / (4 * delta))
    pFix = pAddr + Real.logb 2 ((T^2 + (1 + delta)^2) / (1 + delta)^2) ∧
      2 * Real.logb 2 T - Real.logb 2 (4 * delta) ≤ pFix := by
  dsimp
  have hsplit :=
    paper_conclusion_comoving_endpoint_address_budget_phase_transition T delta hT hdelta
  have h4delta_pos : 0 < 4 * delta := by nlinarith
  have hbudget_arg_pos : 0 < (T ^ 2 + (1 + delta) ^ 2) / (4 * delta) := by
    positivity
  have hbudget_arg_lower :
      T ^ 2 / (4 * delta) ≤ (T ^ 2 + (1 + delta) ^ 2) / (4 * delta) := by
    exact (div_le_div_iff₀ h4delta_pos h4delta_pos).2 (by nlinarith [sq_nonneg (1 + delta)])
  have hlower_arg_pos : 0 < T ^ 2 / (4 * delta) := by
    positivity
  have hlog :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hlower_arg_pos hbudget_arg_lower
  have hlower :
      2 * Real.logb 2 T - Real.logb 2 (4 * delta) ≤
        Omega.TypedAddressBiaxialCompletion.typedAddressWorstCaseBitBudget T delta := by
    have h4delta_ne : (4 * delta : ℝ) ≠ 0 := ne_of_gt h4delta_pos
    have hleft :
        Real.logb 2 (T ^ 2 / (4 * delta)) =
          2 * Real.logb 2 T - Real.logb 2 (4 * delta) := by
      rw [Real.logb_div (show T ^ 2 ≠ 0 by positivity) h4delta_ne, Real.logb_pow]
      norm_num
    simpa [Omega.TypedAddressBiaxialCompletion.typedAddressWorstCaseBitBudget, hleft] using hlog
  constructor
  · linarith
  · exact hlower

end Omega.Conclusion
