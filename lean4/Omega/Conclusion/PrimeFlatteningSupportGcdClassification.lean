import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeCharacterEnergyCenteredVariance

namespace Omega.Conclusion

open Polynomial

/-- Prime flattening on the residue-class slices means that every slice has the same value. -/
def primeFlatteningOnUnitClasses (p : ℕ) (V : PrimeCharacterIndex p → ℂ) : Prop :=
  ∃ z : ℂ, ∀ r, V r = z

/-- Coefficientwise encoding of the shape `F_M(t) = G_p(t^p)`. -/
def primeFlatteningPolynomial (p : ℕ) (F : Polynomial ℂ) : Prop :=
  ∃ G : ℕ → ℂ, ∀ j, F.coeff j = if p ∣ j then G (j / p) else 0

/-- Support-gcd divisibility reformulated coefficientwise: every nonzero index lies in `pℕ`. -/
def primeFlatteningSupportGcdDivisible (p : ℕ) (F : Polynomial ℂ) : Prop :=
  ∀ j, F.coeff j ≠ 0 → p ∣ j

private lemma primeCharacterMean_eq_of_constant {p : ℕ} (hp : Nat.Prime p)
    {V : PrimeCharacterIndex p → ℂ} {z : ℂ} (hV : ∀ r, V r = z) :
    primeCharacterMean p V = z := by
  let total : ℂ := ∑ r, V r
  let den : ℂ := (p - 1 : ℕ)
  have hp_ge : 1 ≤ p := Nat.succ_le_of_lt hp.pos
  have hp1Nat : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  have hden : den ≠ 0 := by simp [den, hp1Nat]
  have hcast : (p : ℂ) - 1 = den := by
    simp [den, Nat.cast_sub hp_ge]
  have htotal : total = den * z := by
    simp [total, den, hV, mul_comm]
  calc
    primeCharacterMean p V = total / den := by
      simp [primeCharacterMean, total, den, hcast]
    _ = (den * z) / den := by rw [htotal]
    _ = z := by field_simp [hden]

private lemma primeFlatteningOnUnitClasses_iff_centeredVariance_zero {p : ℕ} (hp : Nat.Prime p)
    (V : PrimeCharacterIndex p → ℂ) :
    primeFlatteningOnUnitClasses p V ↔ primeCharacterCenteredVariance p V = 0 := by
  constructor
  · rintro ⟨z, hV⟩
    have hMean : primeCharacterMean p V = z := primeCharacterMean_eq_of_constant hp hV
    simp [primeCharacterCenteredVariance, primeCharacterCentered, hV, hMean]
  · intro hVar
    have hzero :
        ∀ r ∈ (Finset.univ : Finset (PrimeCharacterIndex p)),
          ‖primeCharacterCentered p V r‖ ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => by positivity)).mp hVar
    refine ⟨primeCharacterMean p V, ?_⟩
    intro r
    have hr0 : ‖primeCharacterCentered p V r‖ ^ 2 = 0 := hzero r (by simp)
    have hnorm : ‖primeCharacterCentered p V r‖ = 0 := by
      have hnonneg : 0 ≤ ‖primeCharacterCentered p V r‖ := norm_nonneg _
      nlinarith
    have hcenter : primeCharacterCentered p V r = 0 := by
      exact norm_eq_zero.mp hnorm
    exact sub_eq_zero.mp (by simpa [primeCharacterCentered] using hcenter)

private lemma primeFlatteningOnUnitClasses_iff_energy_zero {p : ℕ} (hp : Nat.Prime p)
    (V : PrimeCharacterIndex p → ℂ) :
    primeFlatteningOnUnitClasses p V ↔ primeCharacterEnergy p V = 0 := by
  have hVarEq :
      primeCharacterCenteredVariance p V = primeCharacterEnergy p V :=
    (paper_conclusion_prime_character_energy_centered_variance hp V).2
  rw [← hVarEq]
  exact primeFlatteningOnUnitClasses_iff_centeredVariance_zero hp V

private lemma primeFlatteningPolynomial_iff_supportGcdDivisible {p : ℕ} (hp : Nat.Prime p)
    (F : Polynomial ℂ) :
    primeFlatteningPolynomial p F ↔ primeFlatteningSupportGcdDivisible p F := by
  constructor
  · rintro ⟨G, hG⟩ j hj
    by_cases hpj : p ∣ j
    · exact hpj
    · have hj0 : F.coeff j = 0 := by simpa [hpj] using hG j
      exact (hj hj0).elim
  · intro hSupport
    refine ⟨fun k => F.coeff (p * k), ?_⟩
    intro j
    by_cases hpj : p ∣ j
    · rcases hpj with ⟨k, rfl⟩
      simp [hp.pos]
    · have hj0 : F.coeff j = 0 := by
        by_contra hj0
        exact hpj (hSupport j hj0)
      simp [hpj, hj0]

/-- Formal core of `thm:conclusion-prime-flattening-support-gcd-classification`: constancy of the
unit-class slices is equivalent to vanishing centered energy by the existing centered-variance
theorem; any cyclotomic symmetry criterion can then be supplied as a concrete bridge from zero
energy to the `t ↦ t^p` flattening shape; and the latter is equivalent to the support-gcd
divisibility condition by coefficient inspection. -/
theorem paper_conclusion_prime_flattening_support_gcd_classification {p : ℕ} (hp : Nat.Prime p)
    (V : PrimeCharacterIndex p → ℂ) (F : Polynomial ℂ)
    (hCyclotomicCriterion : primeCharacterEnergy p V = 0 ↔ primeFlatteningPolynomial p F) :
    (primeFlatteningOnUnitClasses p V ↔ primeCharacterEnergy p V = 0) ∧
      (primeCharacterEnergy p V = 0 ↔ primeFlatteningPolynomial p F) ∧
      (primeFlatteningPolynomial p F ↔ primeFlatteningSupportGcdDivisible p F) := by
  exact ⟨primeFlatteningOnUnitClasses_iff_energy_zero hp V, hCyclotomicCriterion,
    primeFlatteningPolynomial_iff_supportGcdDivisible hp F⟩

end Omega.Conclusion
