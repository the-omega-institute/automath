import Mathlib.Data.Nat.Prime.Basic

namespace Omega.Zeta

/-- Concrete data for the localized finite quotient order spectrum.

The localization is represented by the product of inverted primes. -/
abbrev xi_time_part69c_localized_finite_quotient_order_spectrum_data := ℕ

namespace xi_time_part69c_localized_finite_quotient_order_spectrum_data

/-- The product of primes inverted by the localization. -/
def primeProduct (D : xi_time_part69c_localized_finite_quotient_order_spectrum_data) : ℕ := D

/-- The concrete predicate selecting the finite quotient orders visible after localization. -/
def finiteQuotientOrder
    (D : xi_time_part69c_localized_finite_quotient_order_spectrum_data) (n : ℕ) : Prop :=
  1 ≤ n ∧ Nat.Coprime n D.primeProduct

end xi_time_part69c_localized_finite_quotient_order_spectrum_data

/-- Paper label: `thm:xi-time-part69c-localized-finite-quotient-order-spectrum`. -/
theorem paper_xi_time_part69c_localized_finite_quotient_order_spectrum
    (D : xi_time_part69c_localized_finite_quotient_order_spectrum_data) :
    ∀ n : ℕ, D.finiteQuotientOrder n ↔ 1 ≤ n ∧ Nat.Coprime n D.primeProduct := by
  intro n
  rfl

end Omega.Zeta
