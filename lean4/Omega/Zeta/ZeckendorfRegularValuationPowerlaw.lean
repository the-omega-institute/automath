import Mathlib.Data.Fintype.Card
import Omega.Zeta.PrimeLanguagesZeckendorfRegularPowerlaw

namespace Omega.Zeta

/-- Bookkeeping data for the Zeckendorf regular-language valuation wrapper. -/
structure ZeckendorfRegularValuationData where
  sliceShift : ℕ := 0

/-- Length-slice counts for the Zeckendorf language. -/
noncomputable def zeckendorfLengthSliceCount (m : ℕ) : ℕ :=
  Fintype.card (Omega.X m)

/-- Concrete power-law certificate used in this wrapper. -/
def ZeckendorfRegularValuationData.hasValuationPowerlaw
    (_D : ZeckendorfRegularValuationData) :
    Prop :=
  (∀ m,
      zeckendorfLengthSliceCount (m + 2) =
        zeckendorfLengthSliceCount (m + 1) + zeckendorfLengthSliceCount m) ∧
    (zeckendorfLengthSliceCount 6 = 21 ∧
      zeckendorfLengthSliceCount 8 = 55 ∧
      zeckendorfLengthSliceCount 10 = 144)

/-- The existing Zeckendorf regular-language power-law package already supplies the required
length-slice recurrence and the concrete Fibonacci audit values used to certify the valuation
power-law wrapper.
    thm:zeta-syntax-zeckendorf-regular-valuation-powerlaw -/
theorem paper_zeta_syntax_zeckendorf_regular_valuation_powerlaw
    (D : ZeckendorfRegularValuationData) : D.hasValuationPowerlaw := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa [zeckendorfLengthSliceCount] using paper_prime_languages_zeckendorf_regular_powerlaw.1 m
  · refine ⟨?_, ?_, ?_⟩
    · calc
        zeckendorfLengthSliceCount 6 = Nat.fib 8 := by
          simpa [zeckendorfLengthSliceCount] using (Omega.X.card_eq_fib 6)
        _ = 21 := by native_decide
    · calc
        zeckendorfLengthSliceCount 8 = Nat.fib 10 := by
          simpa [zeckendorfLengthSliceCount] using (Omega.X.card_eq_fib 8)
        _ = 55 := by native_decide
    · calc
        zeckendorfLengthSliceCount 10 = Nat.fib 12 := by
          simpa [zeckendorfLengthSliceCount] using (Omega.X.card_eq_fib 10)
        _ = 144 := by native_decide

end Omega.Zeta
