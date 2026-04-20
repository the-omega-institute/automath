import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Zeta.GodelTateAddressPrimitivePeriodicCount

namespace Omega.Zeta

open Finset

/-- The Lee--Yang address tower splits into five disjoint full-shift branches. -/
def derivedLeyangBranchCount : ℕ := 5

/-- Each branch is the full shift on an alphabet of size four. -/
def derivedLeyangAlphabetSize : ℕ := 4

/-- Fixed-point count for the derived Lee--Yang address shift. -/
def derivedLeyangFixedPointCount (n : ℕ) : ℕ :=
  derivedLeyangBranchCount * derivedLeyangAlphabetSize ^ n

/-- Closed form of the Artin--Mazur zeta function for the derived Lee--Yang address shift. -/
def derivedLeyangArtinMazurZeta (z : ℚ) : ℚ :=
  1 / (1 - derivedLeyangAlphabetSize * z) ^ derivedLeyangBranchCount

/-- Möbius-inversion numerator for the primitive orbit counts. -/
def derivedLeyangPrimitiveOrbitNumerator (n : ℕ) : ℤ :=
  (derivedLeyangBranchCount : ℤ) *
    godelTatePrimitivePeriodicPointCount derivedLeyangAlphabetSize n

/-- Primitive orbit count written in the paper's `1/n` normalization. -/
def derivedLeyangPrimitiveOrbitCount (n : ℕ) : ℚ :=
  ((derivedLeyangBranchCount : ℚ) / n) *
    ∑ d ∈ Nat.divisors n, (ArithmeticFunction.moebius d : ℚ) * (derivedLeyangAlphabetSize : ℚ) ^ (n / d)

/-- Closed form of the primitive-orbit Möbius numerator. -/
theorem derivedLeyangPrimitiveOrbitNumerator_closedForm (n : ℕ) :
    derivedLeyangPrimitiveOrbitNumerator n =
      (5 : ℤ) * ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * (4 : ℤ) ^ (n / d) := by
  calc
    derivedLeyangPrimitiveOrbitNumerator n =
        (5 : ℤ) * godelTatePrimitivePeriodicPointCount 4 n := by
          simp [derivedLeyangPrimitiveOrbitNumerator, derivedLeyangBranchCount,
            derivedLeyangAlphabetSize]
    _ = (5 : ℤ) * ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * (4 : ℤ) ^ (n / d) := by
          rw [paper_xi_time_part62c_godel_tate_address_primitive_periodic_count 4 n]
          norm_num

/-- Five disjoint copies of the full `4`-shift have fixed-point counts `5·4^n`, zeta function
`(1 - 4z)^{-5}`, and primitive orbit counts given by the usual Möbius inversion formula.
    thm:derived-leyang-artin-mazur-zeta -/
theorem paper_derived_leyang_artin_mazur_zeta :
    (∀ n : ℕ, derivedLeyangFixedPointCount (n + 1) = 5 * 4 ^ (n + 1)) ∧
      (∀ z : ℚ, derivedLeyangArtinMazurZeta z = 1 / (1 - 4 * z) ^ 5) ∧
      (∀ n : ℕ,
        derivedLeyangPrimitiveOrbitNumerator (n + 1) =
          (5 : ℤ) * ∑ d ∈ Nat.divisors (n + 1), ArithmeticFunction.moebius d * (4 : ℤ) ^ ((n + 1) / d)) ∧
      (∀ n : ℕ,
        derivedLeyangPrimitiveOrbitCount (n + 1) =
          ((5 : ℚ) / (n + 1)) *
            ∑ d ∈ Nat.divisors (n + 1), (ArithmeticFunction.moebius d : ℚ) * (4 : ℚ) ^ ((n + 1) / d)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro z
    rfl
  · intro n
    simpa using derivedLeyangPrimitiveOrbitNumerator_closedForm (n + 1)
  · intro n
    simp [derivedLeyangPrimitiveOrbitCount, derivedLeyangBranchCount, derivedLeyangAlphabetSize]

end Omega.Zeta
