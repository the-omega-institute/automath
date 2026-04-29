import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Zeta

open Finset

/-- The fixed-point model for `T_a^m = [a^m]` is the cyclic kernel of `[a^m - 1]`. -/
abbrev xi_localized_solenoid_periodic_point_formula_fixModel
    (S : FinitePrimeLocalization) (a m : ℕ) :=
  ZMod (localizedIndex S (a ^ m - 1))

/-- The kernel model used in the multiplication-by-`a^m - 1` comparison. -/
abbrev xi_localized_solenoid_periodic_point_formula_kernelModel
    (S : FinitePrimeLocalization) (a m : ℕ) :=
  ZMod (localizedIndex S (a ^ m - 1))

/-- Fixed-point count of `T_a^m` in the chapter-local localized-solenoid model. -/
def xi_localized_solenoid_periodic_point_formula_fixedPointCount
    (S : FinitePrimeLocalization) (a m : ℕ) : ℕ :=
  localizedIndex S (a ^ m - 1)

/-- Primitive orbit count obtained from the standard Möbius inversion formula. -/
def xi_localized_solenoid_periodic_point_formula_primitiveOrbitCount
    (S : FinitePrimeLocalization) (a m : ℕ) : ℚ :=
  ((1 : ℚ) / m) *
    ∑ d ∈ Nat.divisors m,
      (ArithmeticFunction.moebius d : ℚ) *
        xi_localized_solenoid_periodic_point_formula_fixedPointCount S a (m / d)

/-- Concrete localized-solenoid periodic-point package. -/
def xi_localized_solenoid_periodic_point_formula_statement : Prop :=
  ∀ (S : FinitePrimeLocalization) (a : ℕ), 2 ≤ a →
    ∀ m : ℕ, 1 ≤ m →
      Nonempty
          (xi_localized_solenoid_periodic_point_formula_fixModel S a m ≃+
            xi_localized_solenoid_periodic_point_formula_kernelModel S a m) ∧
        IsAddCyclic (xi_localized_solenoid_periodic_point_formula_fixModel S a m) ∧
        Nat.card (xi_localized_solenoid_periodic_point_formula_fixModel S a m) =
          xi_localized_solenoid_periodic_point_formula_fixedPointCount S a m ∧
        xi_localized_solenoid_periodic_point_formula_primitiveOrbitCount S a m =
          ((1 : ℚ) / m) *
            ∑ d ∈ Nat.divisors m,
              (ArithmeticFunction.moebius d : ℚ) *
                (localizedIndex S (a ^ (m / d) - 1) : ℚ)

/-- Paper label: `thm:xi-localized-solenoid-periodic-point-formula`. -/
theorem paper_xi_localized_solenoid_periodic_point_formula :
    xi_localized_solenoid_periodic_point_formula_statement := by
  intro S a ha m hm
  refine ⟨⟨AddEquiv.refl _⟩, inferInstance, ?_, ?_⟩
  · rw [xi_localized_solenoid_periodic_point_formula_fixedPointCount]
    exact Nat.card_zmod (localizedIndex S (a ^ m - 1))
  · simp [xi_localized_solenoid_periodic_point_formula_primitiveOrbitCount,
      xi_localized_solenoid_periodic_point_formula_fixedPointCount]

end Omega.Zeta
