import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Bin-fold degeneracy sector last-bit interval rigidity seed values

Fibonacci values, power-of-two cardinalities, and interval constraints.
-/

namespace Omega.GU

/-- Bin-fold degeneracy sector last-bit interval seeds.
    thm:gut-foldbin-degeneracy-sector-lastbit-interval -/
theorem paper_gut_foldbin_degeneracy_sector_lastbit_interval_seeds :
    (Nat.fib 8 = 21 ∧ Nat.fib 10 = 55) ∧
    (2 ^ 6 = 64) ∧
    (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5) ∧
    (1 ≤ 2 ∧ 2 ≤ 3) ∧
    (Nat.fib 6 = 8 ∧ 16 / 8 = 2) := by
  refine ⟨⟨by native_decide, by native_decide⟩, by norm_num,
         ⟨by decide, by decide⟩, ⟨by omega, by omega⟩,
         ⟨by decide, by omega⟩⟩

end Omega.GU
