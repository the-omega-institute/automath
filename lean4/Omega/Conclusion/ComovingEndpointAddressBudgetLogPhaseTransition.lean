import Mathlib.Tactic
import Omega.Conclusion.ComovingEndpointAddressBudgetPhaseTransition

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-comoving-endpoint-address-budget-log-phase-transition`. The
fixed chart spends two leading base-two logarithmic bits in the height parameter, with the
remaining bounded correction given by the normalized quadratic shoulder. -/
theorem paper_conclusion_comoving_endpoint_address_budget_log_phase_transition
    (T delta : Real) (hT : 1 <= T) (hdelta : 0 < delta) :
    let pFix := Omega.TypedAddressBiaxialCompletion.typedAddressWorstCaseBitBudget T delta
    let pCom := Real.logb 2 (((1 + delta)^2) / (4 * delta))
    pFix - pCom =
      2 * Real.logb 2 T - 2 * Real.logb 2 (1 + delta) +
        Real.logb 2 (1 + ((1 + delta)^2) / T^2) := by
  have hGap :=
    paper_conclusion_comoving_endpoint_address_budget_phase_transition T delta hT hdelta
  dsimp only at hGap ⊢
  rw [hGap]
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT2_ne : T ^ 2 ≠ 0 := by positivity
  have hdelta1_pos : 0 < 1 + delta := by linarith
  have hdelta1_sq_ne : (1 + delta) ^ 2 ≠ 0 := by positivity
  have hshoulder_ne : (1 + (1 + delta) ^ 2 / T ^ 2 : ℝ) ≠ 0 := by positivity
  have hfactor :
      ((T ^ 2 + (1 + delta) ^ 2) / (1 + delta) ^ 2 : ℝ) =
        (T ^ 2 / (1 + delta) ^ 2) * (1 + (1 + delta) ^ 2 / T ^ 2) := by
    field_simp [hT2_ne, hdelta1_sq_ne]
  rw [hfactor]
  rw [Real.logb_mul (show (T ^ 2 / (1 + delta) ^ 2 : ℝ) ≠ 0 by positivity)
      hshoulder_ne]
  rw [Real.logb_div (show (T ^ 2 : ℝ) ≠ 0 by positivity) hdelta1_sq_ne]
  rw [Real.logb_pow, Real.logb_pow]
  ring

end Omega.Conclusion
