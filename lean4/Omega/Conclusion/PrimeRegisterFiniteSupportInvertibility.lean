import Mathlib

namespace Omega.Conclusion

/-- Concrete finitely supported shift-polynomial data. The coefficient family is encoded as an
integer polynomial, i.e. as a finite-support integer stream. -/
structure PrimeRegisterFiniteSupportInvertibilityData where
  polynomial : Polynomial ℤ

/-- Shift-commuting action on finite-support streams, represented as multiplication in `ℤ[X]`. -/
noncomputable def primeRegisterShiftAction (f : Polynomial ℤ) : Polynomial ℤ → Polynomial ℤ :=
  fun g => f * g

/-- Constant-unit criterion on the finitely supported coefficient family. -/
def primeRegisterConstantUnit (f : Polynomial ℤ) : Prop :=
  ∃ u : Units ℤ, f = Polynomial.C (u : ℤ)

/-- Concrete helper theorem: multiplication by a finitely supported coefficient polynomial is
bijective on finite-support streams exactly when the polynomial is a constant unit. -/
theorem prime_register_finite_support_automorphism_iff_constantUnit (f : Polynomial ℤ) :
    Function.Bijective (primeRegisterShiftAction f) ↔ primeRegisterConstantUnit f := by
  constructor
  · intro hAuto
    rcases hAuto.2 1 with ⟨g, hg⟩
    have hUnit : IsUnit f := IsUnit.of_mul_eq_one g (by simpa [primeRegisterShiftAction] using hg)
    rcases Polynomial.isUnit_iff.mp hUnit with ⟨a, ha, hfa⟩
    rcases ha with ⟨u, rfl⟩
    exact ⟨u, hfa.symm⟩
  · rintro ⟨u, rfl⟩
    let U : Units (Polynomial ℤ) := Units.map Polynomial.C.toMonoidHom u
    refine ⟨?_, ?_⟩
    · intro p q hpq
      have hmul := congrArg (fun r : Polynomial ℤ => ↑(U⁻¹) * r) hpq
      simpa [primeRegisterShiftAction, U, mul_assoc] using hmul
    · intro p
      refine ⟨↑(U⁻¹) * p, ?_⟩
      change (U : Polynomial ℤ) * ((↑(U⁻¹) : Polynomial ℤ) * p) = p
      rw [← mul_assoc, Units.mul_inv, one_mul]

/-- Automorphism criterion for the finite-support prime-register action. -/
noncomputable def PrimeRegisterFiniteSupportInvertibilityData.isAutomorphism
    (D : PrimeRegisterFiniteSupportInvertibilityData) : Prop :=
  Function.Bijective (primeRegisterShiftAction D.polynomial)

/-- Constant-unit criterion for the same finite-support action. -/
def PrimeRegisterFiniteSupportInvertibilityData.isConstantUnit
    (D : PrimeRegisterFiniteSupportInvertibilityData) : Prop :=
  primeRegisterConstantUnit D.polynomial

/-- Paper label: `prop:conclusion-prime-register-finite-support-invertibility`. On finite-support
streams, a shift-commuting coefficient family is invertible exactly in the constant-unit case. -/
theorem paper_conclusion_prime_register_finite_support_invertibility
    (D : PrimeRegisterFiniteSupportInvertibilityData) :
    D.isAutomorphism ↔ D.isConstantUnit := by
  simpa [PrimeRegisterFiniteSupportInvertibilityData.isAutomorphism,
    PrimeRegisterFiniteSupportInvertibilityData.isConstantUnit] using
    prime_register_finite_support_automorphism_iff_constantUnit D.polynomial

end Omega.Conclusion
