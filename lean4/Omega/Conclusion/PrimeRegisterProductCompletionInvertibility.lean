import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

namespace Omega.Conclusion

open PowerSeries

noncomputable section

/-- Concrete completed prime-register data encoded by an integer formal power series with unit
constant coefficient and a positive linear term. -/
structure PrimeRegisterProductCompletionData where
  series : PowerSeries ℤ
  constantCoeff_eq_one : PowerSeries.constantCoeff series = 1
  firstCoeff : ℤ
  firstCoeff_pos : 0 < firstCoeff
  coeff_one_eq : PowerSeries.coeff 1 series = firstCoeff

/-- The formal inverse coming from the unit constant coefficient. -/
def PrimeRegisterProductCompletionData.inverseSeries
    (D : PrimeRegisterProductCompletionData) : PowerSeries ℤ :=
  PowerSeries.invOfUnit D.series 1

/-- The completed prime-register action has a two-sided formal inverse. -/
def PrimeRegisterProductCompletionData.has_formal_inverse
    (D : PrimeRegisterProductCompletionData) : Prop :=
  D.series * D.inverseSeries = 1 ∧ D.inverseSeries * D.series = 1

/-- A positive nonconstant coefficient forces the inverse to acquire a negative coefficient. -/
def PrimeRegisterProductCompletionData.inverse_requires_negative_coeff
    (D : PrimeRegisterProductCompletionData) : Prop :=
  PowerSeries.coeff 1 D.inverseSeries < 0

lemma primeRegisterProductCompletion_coeff_one_inverse
    (D : PrimeRegisterProductCompletionData) :
    PowerSeries.coeff 1 D.inverseSeries = -D.firstCoeff := by
  have hcoeff := PowerSeries.coeff_invOfUnit 1 D.series 1
  have hantidiagonal : Finset.antidiagonal 1 = ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
    native_decide
  rw [hantidiagonal] at hcoeff
  simpa [PrimeRegisterProductCompletionData.inverseSeries, D.constantCoeff_eq_one, D.coeff_one_eq,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff

/-- The completed prime-register series has a formal inverse, and a positive first nonconstant
coefficient forces that inverse to contain a negative coefficient. -/
theorem paper_conclusion_prime_register_product_completion_invertibility
    (D : PrimeRegisterProductCompletionData) :
    D.has_formal_inverse ∧ D.inverse_requires_negative_coeff := by
  constructor
  · refine ⟨?_, ?_⟩
    · simpa [PrimeRegisterProductCompletionData.inverseSeries] using
        PowerSeries.mul_invOfUnit D.series 1 D.constantCoeff_eq_one
    · simpa [PrimeRegisterProductCompletionData.inverseSeries] using
        PowerSeries.invOfUnit_mul D.series 1 D.constantCoeff_eq_one
  · rw [PrimeRegisterProductCompletionData.inverse_requires_negative_coeff,
      primeRegisterProductCompletion_coeff_one_inverse]
    simpa using neg_neg_of_pos D.firstCoeff_pos

end

end Omega.Conclusion
