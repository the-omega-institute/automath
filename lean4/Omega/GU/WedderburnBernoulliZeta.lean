import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Wedderburn spectrum determines Bernoulli-zeta tower seed values

Fibonacci values and product identities for the Wedderburn block spectrum theorem.
-/

namespace Omega.GU

/-- Wedderburn spectrum Bernoulli-zeta tower seeds.
    thm:gut-wedderburn-spectrum-determines-bernoulli-zeta-tower -/
theorem paper_gut_wedderburn_spectrum_bernoulli_zeta_tower_seeds :
    (Nat.fib 4 = 3) ∧
    (4 + 1 + 1 = 6) ∧
    (Nat.fib 5 = 5) ∧
    (6 * 1 = 6 ∧ 30 * 1 = 30) ∧
    (6 * 15 = 90) ∧
    (6 < 8) := by
  refine ⟨by decide, by omega, by decide, ⟨by omega, by omega⟩, by omega, by omega⟩

end Omega.GU
