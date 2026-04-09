import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Audited even-window minimum-sector budget uniqueness

For audited even windows m ∈ {6, 8, 10, 12}, the minimum degeneracy
budget is B_m = F(m/2) · F(m). Only m = 6 achieves B_m = 16.
-/

namespace Omega.GU.MinSectorBudget

/-- Budget values: B_m = F(m/2) · F(m) for m ∈ {6, 8, 10, 12}.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem budget_values :
    Nat.fib 3 * Nat.fib 6 = 16 ∧
    Nat.fib 4 * Nat.fib 8 = 63 ∧
    Nat.fib 5 * Nat.fib 10 = 275 ∧
    Nat.fib 6 * Nat.fib 12 = 1152 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Only m = 6 achieves B_m = 16 among audited even windows.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem paper_gut_budget16_unique_m6 :
    Nat.fib 3 * Nat.fib 6 = 16 ∧
    Nat.fib 4 * Nat.fib 8 ≠ 16 ∧
    Nat.fib 5 * Nat.fib 10 ≠ 16 ∧
    Nat.fib 6 * Nat.fib 12 ≠ 16 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The minimum degeneracy values d_min(m) = F(m/2).
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem dmin_values :
    Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧ Nat.fib 6 = 8 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The sector sizes |S_{m,d_min}| = F(m).
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem sector_sizes :
    Nat.fib 6 = 8 ∧ Nat.fib 8 = 21 ∧ Nat.fib 10 = 55 ∧ Nat.fib 12 = 144 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Window-6 additional identities: sector size, budget, complement.
    thm:gut-audited-even-windows-unique-budget16-min-sector -/
theorem window6_sector_identities :
    Nat.fib 6 = 8 ∧
    Nat.fib 3 * Nat.fib 6 = 16 ∧
    Nat.fib 8 - Nat.fib 6 = 13 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-! ### Double Fibonacci minsector budget threshold -/

/-- F(m/2) * F(m) ≤ 2^m for even m ∈ {6,8,10,12,14,16,18,20}.
    thm:gut-foldbin-double-fibonacci-minsector-budget-threshold -/
theorem paper_gut_foldbin_double_fibonacci_minsector_budget :
    (∀ m ∈ ({6, 8, 10, 12, 14, 16, 18, 20} : Finset Nat),
      Nat.fib (m / 2) * Nat.fib m ≤ 2 ^ m) ∧
    Nat.fib 3 * Nat.fib 6 = 16 ∧
    Nat.fib 10 * Nat.fib 20 = 372075 := by
  refine ⟨by intro m hm; fin_cases hm <;> native_decide,
          by native_decide, by native_decide⟩

end Omega.GU.MinSectorBudget
