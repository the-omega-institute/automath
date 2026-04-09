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

/-- Stirling-Bernoulli jet rigidity seeds.
    thm:gut-logCm-stirling-bernoulli-jet-rigidity -/
theorem paper_gut_stirling_bernoulli_jet_rigidity_seeds :
    (6 * 1 = 6 ∧ 30 * 1 = 30 ∧ 42 * 1 = 42) ∧
    (2 * 1 = 2 ∧ 2 * 2 = 4 ∧ 2 * 3 = 6) ∧
    (6 = 6 ∧ 90 = 6 * 15 ∧ 945 = 63 * 15) ∧
    (Nat.factorial 1 = 1 ∧ Nat.factorial 2 = 2 ∧ Nat.factorial 3 = 6) ∧
    (1 ≤ 1 ∧ 2 ≤ 2 ∧ 3 ≤ 3) := by
  exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega⟩, ⟨by decide, by decide, by decide⟩,
         ⟨by omega, by omega, by omega⟩⟩

/-- Pole-ladder even-zeta seeds.
    thm:gut-logCm-pole-ladder-evenzeta -/
theorem paper_gut_logCm_pole_ladder_evenzeta_seeds :
    (4 + 16 = 20) ∧
    (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
    (6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189) ∧
    (1 < 2) ∧
    (6 < 7) := by
  omega

end Omega.GU
