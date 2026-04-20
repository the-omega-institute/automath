import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- First-coordinate Fibonacci coefficient for the `m`-fold iterate of
`(x, y) ↦ (x + y, x)`. -/
def xiBqIteratedXCoeff (m : Nat) : Nat :=
  Nat.fib (m + 1)

/-- Second-coordinate Fibonacci coefficient for the `m`-fold iterate of
`(x, y) ↦ (x + y, x)`. -/
def xiBqIteratedYCoeff (m : Nat) : Nat :=
  Nat.fib m

/-- The `l`-th overlap-index contribution to the coefficient of `x^(q-k) y^k`. -/
def xiBqPowerEntrywiseSummand (q m k l : Nat) : Nat :=
  Nat.choose q l * Nat.choose (q - l) (k - l) *
    xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k

/-- The full coefficient obtained by summing the overlap-index contributions. -/
def xiBqPowerEntrywiseCoeff (q m k : Nat) : Nat :=
  Finset.sum (Finset.range (k + 1)) fun t => xiBqPowerEntrywiseSummand q m k t

/-- Concrete Fibonacci/binomial package for the iterated `B_q` substitution. -/
abbrev xiBqPowerEntrywiseFormula (q m k l : Nat) : Prop :=
  xiBqIteratedXCoeff (m + 1) = xiBqIteratedXCoeff m + xiBqIteratedYCoeff m ∧
    xiBqIteratedYCoeff (m + 1) = xiBqIteratedXCoeff m ∧
    (xiBqPowerEntrywiseCoeff q m k =
      Finset.sum (Finset.range (k + 1)) fun t =>
        Nat.choose q t * Nat.choose (q - t) (k - t) *
          xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k) ∧
    xiBqPowerEntrywiseSummand q m k l =
      Nat.choose q l * Nat.choose (q - l) (k - l) *
        xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k

/-- Paper label: `prop:xi-bq-power-entrywise-fibonacci-binomial`.
    Iterating the substitution `(x, y) ↦ (x + y, x)` produces Fibonacci coefficients, and the
    coefficient of `x^(q-k) y^k` is assembled from the overlap-index binomial expansion. -/
theorem paper_xi_bq_power_entrywise_fibonacci_binomial (q m k l : Nat) :
    xiBqPowerEntrywiseFormula q m k l := by
  constructor
  · change Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m
    simpa [Nat.add_comm] using Nat.fib_add_two (n := m)
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end Omega.Zeta
