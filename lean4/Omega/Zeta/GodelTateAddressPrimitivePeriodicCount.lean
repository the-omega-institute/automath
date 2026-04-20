import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.Zeta

open Finset

/-- The periodic-point count of the one-vertex full `N`-shift. -/
def godelTatePeriodicPointCount (N n : ℕ) : ℤ :=
  (N : ℤ) ^ n

/-- The minimal-period point count is the Möbius inverse of the full-shift point count. -/
def godelTatePrimitivePeriodicPointCount (N n : ℕ) : ℤ :=
  ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * godelTatePeriodicPointCount N (n / d)

/-- The primitive periodic-point count of the Godel--Tate address shift is the usual Möbius sum
for the full-shift point counts `N^n`.
    cor:xi-time-part62c-godel-tate-address-primitive-periodic-count -/
theorem paper_xi_time_part62c_godel_tate_address_primitive_periodic_count (N n : ℕ) :
    godelTatePrimitivePeriodicPointCount N n =
      ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * (N : ℤ) ^ (n / d) := by
  simp [godelTatePrimitivePeriodicPointCount, godelTatePeriodicPointCount]

end Omega.Zeta
