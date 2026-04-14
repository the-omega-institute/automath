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

end Omega.GU.NapSo10AnalyticMinimality
