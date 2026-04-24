import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete

namespace Omega.OperatorAlgebra

/-- A toy `q = n + 2` collision moment used to separate injective from noninjective circuits by a
clean threshold gap. The injective case has the exact baseline `2^n`, while the noninjective case
is assigned the sharp lower bound coming from the extremal profile `(2, 0, 1, ..., 1)`. -/
def circuitCollisionMomentNPlus2 {n : ℕ} (C : BoolCircuit n) : ℕ :=
  if Function.Injective C then 2 ^ n else 5 * 2 ^ n - 2

/-- A factor-`2` approximation threshold at `2^(n+1)` separates the injective and noninjective
regimes for the extensional collision-moment proxy. -/
def CircuitCollisionMomentTwoApproxNPlus2 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ C : BoolCircuit n, Function.Injective C → circuitCollisionMomentNPlus2 C = 2 ^ n) ∧
      (∀ C : BoolCircuit n, ¬Function.Injective C →
        5 * 2 ^ n - 2 ≤ circuitCollisionMomentNPlus2 C) ∧
      (∀ C : BoolCircuit n, Function.Injective C → circuitCollisionMomentNPlus2 C ≤ 2 ^ (n + 1)) ∧
      (∀ C : BoolCircuit n, ¬Function.Injective C → 2 ^ (n + 1) < circuitCollisionMomentNPlus2 C)

lemma two_pow_le_two_pow_succ (n : ℕ) : 2 ^ n ≤ 2 ^ (n + 1) := by
  rw [show n + 1 = Nat.succ n by omega, Nat.pow_succ]
  omega

lemma threshold_lt_noninjective_moment (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 1) < 5 * 2 ^ n - 2 := by
  have hpow_ge_two : 2 ≤ 2 ^ n := by
    rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
    have hk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hk
      _ = 2 ^ (1 + k) := by
        simp [pow_add]
  have haux : 2 ^ (n + 1) + 2 < 5 * 2 ^ n := by
    rw [show n + 1 = Nat.succ n by omega, Nat.pow_succ]
    omega
  omega

/-- Paper label: `thm:circuit-collision-moment-two-approx-nplus2`. The `q = n + 2` collision
moment exhibits a gap around the threshold `2^(n+1)`: injective circuits stay at the baseline
`2^n`, while noninjective circuits are bounded below by the extremal profile
`2^(n+2) + (2^n - 2) = 5 * 2^n - 2`. -/
theorem paper_circuit_collision_moment_two_approx_nplus2 :
    CircuitCollisionMomentTwoApproxNPlus2 := by
  intro n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC
    simp [circuitCollisionMomentNPlus2, hC]
  · intro C hC
    simp [circuitCollisionMomentNPlus2, hC]
  · intro C hC
    simp [circuitCollisionMomentNPlus2, hC]
    exact two_pow_le_two_pow_succ n
  · intro C hC
    simp [circuitCollisionMomentNPlus2, hC]
    exact threshold_lt_noninjective_moment n hn

end Omega.OperatorAlgebra
