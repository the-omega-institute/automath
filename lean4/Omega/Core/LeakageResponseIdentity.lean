import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.POM

/-- Ziggurat leakage constant: λ_ZT = (1 + √5) / 2 (golden ratio).
    thm:pom-leakage-response-identity -/
noncomputable def lambdaZT : ℝ := (1 + Real.sqrt 5) / 2

/-- Ziggurat response constant: χ_ZT = 3 − λ_ZT = (5 − √5) / 2.
    thm:pom-leakage-response-identity -/
noncomputable def chiZT : ℝ := 3 - lambdaZT

/-- Even-index ziggurat entropy increment.
    thm:pom-leakage-response-identity -/
noncomputable def iEven : ℝ := 1 - chiZT * Real.logb 2 lambdaZT

/-- Odd-index ziggurat entropy increment.
    thm:pom-leakage-response-identity -/
noncomputable def iOdd : ℝ := iEven / 2

/-- Explicit form of λ_ZT.
    thm:pom-leakage-response-identity -/
theorem lambdaZT_eq : lambdaZT = (1 + Real.sqrt 5) / 2 := rfl

/-- Symbolic form χ = 3 − λ.
    thm:pom-leakage-response-identity -/
theorem chiZT_eq_three_sub_lambdaZT : chiZT = 3 - lambdaZT := rfl

/-- Closed form χ_ZT = (5 − √5) / 2.
    thm:pom-leakage-response-identity -/
theorem chiZT_explicit : chiZT = (5 - Real.sqrt 5) / 2 := by
  unfold chiZT lambdaZT
  ring

/-- λ_ZT is positive.
    thm:pom-leakage-response-identity -/
theorem lambdaZT_pos : 0 < lambdaZT := by
  unfold lambdaZT
  have : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  linarith

/-- Odd increment is half the even increment (definitional).
    thm:pom-leakage-response-identity -/
theorem iOdd_eq_iEven_div_two : iOdd = iEven / 2 := rfl

/-- Closed form for I_even.
    thm:pom-leakage-response-identity -/
theorem iEven_explicit : iEven = 1 - chiZT * Real.logb 2 lambdaZT := rfl

/-- Closed form for I_odd.
    thm:pom-leakage-response-identity -/
theorem iOdd_explicit :
    iOdd = (1 - chiZT * Real.logb 2 lambdaZT) / 2 := by
  unfold iOdd iEven
  rfl

/-- Paper package: POM leakage/response-constant identity.
    thm:pom-leakage-response-identity -/
theorem paper_pom_leakage_response_identity :
    lambdaZT = (1 + Real.sqrt 5) / 2 ∧
    chiZT = 3 - lambdaZT ∧
    chiZT = (5 - Real.sqrt 5) / 2 ∧
    0 < lambdaZT ∧
    iEven = 1 - chiZT * Real.logb 2 lambdaZT ∧
    iOdd = iEven / 2 ∧
    iOdd = (1 - chiZT * Real.logb 2 lambdaZT) / 2 :=
  ⟨lambdaZT_eq, chiZT_eq_three_sub_lambdaZT, chiZT_explicit, lambdaZT_pos,
   iEven_explicit, iOdd_eq_iEven_div_two, iOdd_explicit⟩

end Omega.POM
