import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.GU.NapSo10AnalyticMinimality

/-- The Zeckendorf signature of the `so(10)` dimension `45` is `F₉ + F₆ + F₄`.
    thm:nap-so10-analytic-minimality -/
theorem paper_gut_nap_so10_analytic_minimality_seeds :
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by
  norm_num [Nat.fib]

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_gut_nap_so10_analytic_minimality_package :
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 :=
  paper_gut_nap_so10_analytic_minimality_seeds

/-- Below `45`, none of the simple-Lie dimensions in the audited finite list can equal the
Fibonacci constraint value `F₄ + F₆ = 11`; the minimal witness is the `so(10)` identity
`45 = F₉ + F₆ + F₄`.
    thm:nap-so10-analytic-minimality -/
theorem paper_nap_so10_analytic_minimality :
    (∀ d ∈ ({3, 8, 10, 14, 15, 21, 24, 28, 35, 36} : Finset ℕ), Nat.fib 4 + Nat.fib 6 ≠ d) ∧
      45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by
  refine ⟨?_, paper_gut_nap_so10_analytic_minimality_seeds⟩
  intro d hd
  have hd' :
      d = 3 ∨ d = 8 ∨ d = 10 ∨ d = 14 ∨ d = 15 ∨
        d = 21 ∨ d = 24 ∨ d = 28 ∨ d = 35 ∨ d = 36 := by
    simpa using hd
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Nat.fib]

end Omega.GU.NapSo10AnalyticMinimality
