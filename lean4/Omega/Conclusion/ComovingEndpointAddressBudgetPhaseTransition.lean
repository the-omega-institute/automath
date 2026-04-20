import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingBitBudget

namespace Omega.Conclusion

/-- The fixed-chart worst-case bit budget differs from the comoving one by the exact logarithm of
the quadratic height-window overhead. -/
theorem paper_conclusion_comoving_endpoint_address_budget_phase_transition
    (T delta : Real) (hT : 1 <= T) (hdelta : 0 < delta) :
    let pFix := Omega.TypedAddressBiaxialCompletion.typedAddressWorstCaseBitBudget T delta
    let pCom := Real.logb 2 (((1 + delta)^2) / (4 * delta))
    pFix - pCom = Real.logb 2 ((T^2 + (1 + delta)^2) / (1 + delta)^2) := by
  dsimp [Omega.TypedAddressBiaxialCompletion.typedAddressWorstCaseBitBudget]
  have hden_ne : (4 * delta : ℝ) ≠ 0 := by linarith
  have hratio_ne : ((1 + delta) ^ 2 / (4 * delta) : ℝ) ≠ 0 := by positivity
  have hpow_ne : ((1 + delta) ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← Real.logb_div
    (show ((T ^ 2 + (1 + delta) ^ 2) / (4 * delta) : ℝ) ≠ 0 by positivity) hratio_ne]
  rw [show
      ((T ^ 2 + (1 + delta) ^ 2) / (4 * delta)) / (((1 + delta) ^ 2) / (4 * delta)) =
        (T ^ 2 + (1 + delta) ^ 2) / (1 + delta) ^ 2 by
      field_simp [hden_ne, hpow_ne]
      ]

end Omega.Conclusion
