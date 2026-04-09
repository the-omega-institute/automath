import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.GU.BoundaryTowerFibCount

open Nat

/-- Fibonacci seed values: fib 2 = 1, fib 3 = 2, ..., fib 8 = 21.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem fib_seeds :
    Nat.fib 2 = 1 ∧ Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧
    Nat.fib 5 = 5 ∧ Nat.fib 6 = 8 ∧ Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- SM signature sum: fib 2 + fib 4 + fib 6 = 12.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem sm_signature_sum : Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 := by native_decide

/-- Square margin: fib 8 - (fib 2 + fib 4 + fib 6) = (fib 4)².
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem square_margin : Nat.fib 8 - (Nat.fib 2 + Nat.fib 4 + Nat.fib 6) = Nat.fib 4 ^ 2 := by
  native_decide

/-- Boundary less than total: fib(2k) < fib(2k+2) for k = 2..5.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem bdry_lt_total :
    Nat.fib 4 < Nat.fib 6 ∧
    Nat.fib 6 < Nat.fib 8 ∧
    Nat.fib 8 < Nat.fib 10 ∧
    Nat.fib 10 < Nat.fib 12 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Paper package: boundary tower Fibonacci count seeds.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem paper_boundary_tower_fib_count :
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 ∧
    Nat.fib 8 - 12 = Nat.fib 4 ^ 2 ∧
    (Nat.fib 4 < Nat.fib 6 ∧ Nat.fib 6 < Nat.fib 8 ∧
     Nat.fib 8 < Nat.fib 10 ∧ Nat.fib 10 < Nat.fib 12) :=
  ⟨sm_signature_sum, by native_decide, bdry_lt_total⟩

end Omega.GU.BoundaryTowerFibCount
