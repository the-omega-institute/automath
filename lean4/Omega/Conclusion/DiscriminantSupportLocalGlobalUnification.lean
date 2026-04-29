import Mathlib.Tactic

namespace Omega.Conclusion

/-- The concrete Hankel/discriminant factor used by the local-global support seed. -/
def conclusion_discriminant_support_local_global_unification_hankelDiscriminant
    (weightProduct discriminant : ℤ) : ℤ :=
  weightProduct * discriminant

/-- The negative-spectrum product has the same arithmetic support in this seed model. -/
def conclusion_discriminant_support_local_global_unification_negativeSpectrumProduct
    (weightProduct discriminant : ℤ) : ℤ :=
  conclusion_discriminant_support_local_global_unification_hankelDiscriminant
    weightProduct discriminant

/-- A prime is good exactly when it does not divide the common Hankel/discriminant factor. -/
def conclusion_discriminant_support_local_global_unification_goodPrime
    (p : ℕ) (weightProduct discriminant : ℤ) : Prop :=
  ¬ (p : ℤ) ∣
    conclusion_discriminant_support_local_global_unification_hankelDiscriminant
      weightProduct discriminant

/-- The bad-prime support attached to the common discriminant factor. -/
def conclusion_discriminant_support_local_global_unification_badPrimeSupport
    (weightProduct discriminant : ℤ) : Set ℕ :=
  {p | Nat.Prime p ∧
    (p : ℤ) ∣
      conclusion_discriminant_support_local_global_unification_hankelDiscriminant
        weightProduct discriminant}

/-- Concrete local-global unification statement: the Archimedean negative-spectrum product and
the non-Archimedean good-prime criterion use the same discriminant support. -/
def conclusion_discriminant_support_local_global_unification_statement : Prop :=
  ∀ weightProduct discriminant : ℤ,
    conclusion_discriminant_support_local_global_unification_badPrimeSupport
        weightProduct discriminant =
      {p | Nat.Prime p ∧
        (p : ℤ) ∣
          conclusion_discriminant_support_local_global_unification_negativeSpectrumProduct
            weightProduct discriminant} ∧
      ∀ p : ℕ,
        Nat.Prime p →
          (p ∈ conclusion_discriminant_support_local_global_unification_badPrimeSupport
              weightProduct discriminant ↔
            ¬ conclusion_discriminant_support_local_global_unification_goodPrime
              p weightProduct discriminant)

/-- Paper label: `thm:conclusion-discriminant-support-local-global-unification`. -/
theorem paper_conclusion_discriminant_support_local_global_unification :
    conclusion_discriminant_support_local_global_unification_statement := by
  intro weightProduct discriminant
  constructor
  · ext p
    simp [conclusion_discriminant_support_local_global_unification_badPrimeSupport,
      conclusion_discriminant_support_local_global_unification_negativeSpectrumProduct]
  · intro p hp
    simp [conclusion_discriminant_support_local_global_unification_badPrimeSupport,
      conclusion_discriminant_support_local_global_unification_goodPrime, hp]

end Omega.Conclusion
