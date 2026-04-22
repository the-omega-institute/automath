import Mathlib.Tactic
import Omega.FoldComputability.HaltingNoUniformLearning

namespace Omega.FoldComputability

/-- Concrete halting-time package for the uniform circuit family used in the first-collision
reduction.  The boolean flag says whether the simulated machine halts; if it does, `haltTime` is
the first stage at which the generator switches from the identity circuit to the constant one. -/
structure fold_computability_uniform_circuit_first_collision_time_data where
  fold_computability_uniform_circuit_first_collision_time_halts : Bool
  fold_computability_uniform_circuit_first_collision_time_haltTime : ℕ

/-- Width of the `t`-th circuit in the uniform family. -/
def fold_computability_uniform_circuit_first_collision_time_width (t : ℕ) : ℕ := t + 1

/-- Identity circuit on the width-`t+1` fiber. -/
def fold_computability_uniform_circuit_first_collision_time_identity
    (t : ℕ) :
    (Fin (fold_computability_uniform_circuit_first_collision_time_width t) → Bool) →
      (Fin (fold_computability_uniform_circuit_first_collision_time_width t) → Bool) :=
  fun w => w

/-- Constant-false circuit on the width-`t+1` fiber. -/
def fold_computability_uniform_circuit_first_collision_time_constant_false
    (t : ℕ) :
    (Fin (fold_computability_uniform_circuit_first_collision_time_width t) → Bool) →
      (Fin (fold_computability_uniform_circuit_first_collision_time_width t) → Bool) :=
  fun _ _ => false

/-- The `t`-th circuit: identity before the threshold, constant false afterward. -/
def fold_computability_uniform_circuit_first_collision_time_circuit
    (D : fold_computability_uniform_circuit_first_collision_time_data) (t : ℕ) :
    (Fin (fold_computability_uniform_circuit_first_collision_time_width t) → Bool) →
      (Fin (fold_computability_uniform_circuit_first_collision_time_width t) → Bool) :=
  if D.fold_computability_uniform_circuit_first_collision_time_halts &&
        decide (D.fold_computability_uniform_circuit_first_collision_time_haltTime ≤ t) then
    fold_computability_uniform_circuit_first_collision_time_constant_false t
  else
    fold_computability_uniform_circuit_first_collision_time_identity t

/-- Maximum fiber size of the generated circuit.  For the identity map the fibers are singletons;
for the constant map the unique nonempty fiber has full size `2^{t+1}`. -/
def fold_computability_uniform_circuit_first_collision_time_max_fiber
    (D : fold_computability_uniform_circuit_first_collision_time_data) (t : ℕ) : ℕ :=
  if D.fold_computability_uniform_circuit_first_collision_time_halts &&
        decide (D.fold_computability_uniform_circuit_first_collision_time_haltTime ≤ t) then
    2 ^ fold_computability_uniform_circuit_first_collision_time_width t
  else
    1

/-- The first collision time, recorded as an optional threshold: `none` means no collision ever
appears, `some T` means the first collision occurs exactly at time `T`. -/
def fold_computability_uniform_circuit_first_collision_time_first_collision_time
    (D : fold_computability_uniform_circuit_first_collision_time_data) : Option ℕ :=
  if D.fold_computability_uniform_circuit_first_collision_time_halts then
    some D.fold_computability_uniform_circuit_first_collision_time_haltTime
  else
    none

/-- Paper-facing summary of the uniform collision-time reduction. -/
def fold_computability_uniform_circuit_first_collision_time_statement
    (D : fold_computability_uniform_circuit_first_collision_time_data) : Prop :=
  (D.fold_computability_uniform_circuit_first_collision_time_halts = false →
      ∀ t : ℕ,
        (fold_computability_uniform_circuit_first_collision_time_circuit D t =
            fold_computability_uniform_circuit_first_collision_time_identity t) ∧
          fold_computability_uniform_circuit_first_collision_time_max_fiber D t = 1) ∧
    (D.fold_computability_uniform_circuit_first_collision_time_halts = true →
      (∀ t : ℕ,
        t < D.fold_computability_uniform_circuit_first_collision_time_haltTime →
          (fold_computability_uniform_circuit_first_collision_time_circuit D t =
              fold_computability_uniform_circuit_first_collision_time_identity t) ∧
            fold_computability_uniform_circuit_first_collision_time_max_fiber D t = 1) ∧
      ∀ t : ℕ,
        D.fold_computability_uniform_circuit_first_collision_time_haltTime ≤ t →
          (fold_computability_uniform_circuit_first_collision_time_circuit D t =
              fold_computability_uniform_circuit_first_collision_time_constant_false t) ∧
            (fold_computability_uniform_circuit_first_collision_time_max_fiber D t =
                2 ^ fold_computability_uniform_circuit_first_collision_time_width t) ∧
            2 ≤ fold_computability_uniform_circuit_first_collision_time_max_fiber D t) ∧
    (fold_computability_uniform_circuit_first_collision_time_first_collision_time D =
      if D.fold_computability_uniform_circuit_first_collision_time_halts then
        some D.fold_computability_uniform_circuit_first_collision_time_haltTime
      else
        none) ∧
    ((∃ t : ℕ,
        2 ≤ fold_computability_uniform_circuit_first_collision_time_max_fiber D t) ↔
      D.fold_computability_uniform_circuit_first_collision_time_halts = true)

/-- Paper label: `thm:fold-computability-uniform-circuit-first-collision-time`. -/
theorem paper_fold_computability_uniform_circuit_first_collision_time
    (D : fold_computability_uniform_circuit_first_collision_time_data) :
    fold_computability_uniform_circuit_first_collision_time_statement D := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro hhalts t
    simp [fold_computability_uniform_circuit_first_collision_time_circuit,
      fold_computability_uniform_circuit_first_collision_time_max_fiber, hhalts]
  · intro hhalts
    refine ⟨?_, ?_⟩
    · intro t ht
      have hnot_le :
          ¬ D.fold_computability_uniform_circuit_first_collision_time_haltTime ≤ t :=
        Nat.not_le_of_gt ht
      simp [fold_computability_uniform_circuit_first_collision_time_circuit,
        fold_computability_uniform_circuit_first_collision_time_max_fiber, hhalts, hnot_le]
    · intro t ht
      have htwo_le_pow :
          2 ≤ 2 ^ fold_computability_uniform_circuit_first_collision_time_width t := by
        have hpow_pos : 0 < 2 ^ t := pow_pos (by decide) t
        have hpow_ge_one : 1 ≤ 2 ^ t := Nat.succ_le_of_lt hpow_pos
        have hmul :
            2 * 1 ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 hpow_ge_one
        simpa [fold_computability_uniform_circuit_first_collision_time_width, pow_succ] using hmul
      simp [fold_computability_uniform_circuit_first_collision_time_circuit,
        fold_computability_uniform_circuit_first_collision_time_max_fiber,
        hhalts, ht, htwo_le_pow]
  · constructor
    · intro h
      by_cases hhalts : D.fold_computability_uniform_circuit_first_collision_time_halts = true
      · exact hhalts
      · rcases h with ⟨t, ht⟩
        simp [fold_computability_uniform_circuit_first_collision_time_max_fiber, hhalts] at ht
    · intro hhalts
      refine ⟨D.fold_computability_uniform_circuit_first_collision_time_haltTime, ?_⟩
      have htwo_le_pow :
          2 ≤
            2 ^
              fold_computability_uniform_circuit_first_collision_time_width
                D.fold_computability_uniform_circuit_first_collision_time_haltTime := by
        have hpow_pos : 0 < 2 ^ D.fold_computability_uniform_circuit_first_collision_time_haltTime :=
          pow_pos (by decide) D.fold_computability_uniform_circuit_first_collision_time_haltTime
        have hpow_ge_one :
            1 ≤ 2 ^ D.fold_computability_uniform_circuit_first_collision_time_haltTime :=
          Nat.succ_le_of_lt hpow_pos
        have hmul :
            2 * 1 ≤ 2 * 2 ^ D.fold_computability_uniform_circuit_first_collision_time_haltTime :=
          Nat.mul_le_mul_left 2 hpow_ge_one
        simpa [fold_computability_uniform_circuit_first_collision_time_width, pow_succ] using hmul
      simpa [fold_computability_uniform_circuit_first_collision_time_max_fiber, hhalts]

end Omega.FoldComputability
