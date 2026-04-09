import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Bernoulli-zeta tower arithmetic subsequence rigidity seed values

Arithmetic identities for the log(C_m) arithmetic subsequence rigidity theorem.
-/

namespace Omega.GU

/-- Bernoulli-zeta tower arithmetic subsequence rigidity seeds.
    thm:gut-logCm-arithmetic-subsequence-rigidity -/
theorem paper_gut_logCm_arithmetic_subsequence_rigidity_seeds :
    (4 + 16 = 20) ∧
    (6 * 1 = 6) ∧
    (2 * 2 = 4 ∧ 1 * 6 = 6) ∧
    (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
    (∀ n : Nat, 0 + 1 * n = n) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3) := by
  exact ⟨by omega, by omega, ⟨by omega, by omega⟩,
         ⟨by omega, by omega, by omega⟩, fun n => by omega,
         ⟨by decide, by decide⟩⟩

end Omega.GU
