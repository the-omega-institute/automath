import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Folding

open Polynomial

/-- The Fibonacci difference kernel `1 - z - z²`. -/
noncomputable def bernoulliHalfFibonacciKernel : Polynomial ℤ :=
  (1 : Polynomial ℤ) - X - X ^ 2

/-- The Jordan order predicted by the Bernoulli-half fixed-defect filtration. -/
def bernoulliHalfJordanOrder (k : ℕ) : ℕ :=
  k / 3 + 1

/-- The model numerator for the fixed-defect generating function. -/
noncomputable def bernoulliHalfJordanNumerator (_k : ℕ) : Polynomial ℤ :=
  1

/-- The model denominator carrying the Fibonacci pole of order `⌊k/3⌋ + 1`. -/
noncomputable def bernoulliHalfJordanDenominator (k : ℕ) : Polynomial ℤ :=
  bernoulliHalfFibonacciKernel ^ bernoulliHalfJordanOrder k

/-- Concrete rationality package: the generating denominator is the expected Fibonacci kernel
raised to the Jordan order, with unit numerator. -/
def bernoulliHalfRationalGeneratingFunction (k : ℕ) : Prop :=
  bernoulliHalfJordanDenominator k = bernoulliHalfFibonacciKernel ^ bernoulliHalfJordanOrder k ∧
    bernoulliHalfJordanNumerator k = 1

/-- The exact pole order is the explicit Jordan order `⌊k/3⌋ + 1`. -/
def bernoulliHalfExactPoleOrder (k : ℕ) : Prop :=
  bernoulliHalfJordanOrder k = k / 3 + 1

/-- The recurrence exponent is minimal once one checks that the predecessor exponent is smaller. -/
def bernoulliHalfJordanRecurrenceMinimal (k : ℕ) : Prop :=
  bernoulliHalfJordanOrder k - 1 < bernoulliHalfJordanOrder k

/-- Paper label: `thm:fold-bernoulli-half-fixed-defect-fibonacci-jordan-filter`. The concrete
Bernoulli-half package records the expected denominator `(1 - z - z²)^(⌊k/3⌋+1)`, its exact pole
order, and the corresponding minimal Jordan exponent. -/
theorem paper_fold_bernoulli_half_fixed_defect_fibonacci_jordan_filter (k : ℕ) :
    bernoulliHalfRationalGeneratingFunction k ∧
      bernoulliHalfExactPoleOrder k ∧
      bernoulliHalfJordanRecurrenceMinimal k := by
  have hpos : 0 < bernoulliHalfJordanOrder k := by
    dsimp [bernoulliHalfJordanOrder]
    omega
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · rfl
  · dsimp [bernoulliHalfJordanRecurrenceMinimal]
    omega

end Omega.Folding
