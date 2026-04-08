import Mathlib.Tactic

namespace Omega.EA

open Finset

/-- Primitive trace: sum over divisors `n` of `m` of `n · p n`.
    prop:time-space-commuting-diagram -/
noncomputable def primitiveTrace (p : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ n ∈ m.divisors, n * p n

/-- Primitive trace at `0` is `0` (no divisors).
    prop:time-space-commuting-diagram -/
theorem primitiveTrace_zero (p : ℕ → ℕ) : primitiveTrace p 0 = 0 := by
  unfold primitiveTrace
  simp

/-- Primitive trace at `1` equals `p 1`.
    prop:time-space-commuting-diagram -/
theorem primitiveTrace_one (p : ℕ → ℕ) : primitiveTrace p 1 = p 1 := by
  unfold primitiveTrace
  simp

/-- Primitive trace at a prime `q` equals `p 1 + q · p q`.
    prop:time-space-commuting-diagram -/
theorem primitiveTrace_prime (p : ℕ → ℕ) (q : ℕ) (hq : Nat.Prime q) :
    primitiveTrace p q = p 1 + q * p q := by
  unfold primitiveTrace
  rw [Nat.Prime.divisors hq]
  rw [Finset.sum_insert (by simp [hq.one_lt.ne])]
  simp

/-- Primitive trace is monotone in the coefficient function.
    prop:time-space-commuting-diagram -/
theorem primitiveTrace_mono (p p' : ℕ → ℕ) (m : ℕ)
    (hp : ∀ n, p n ≤ p' n) :
    primitiveTrace p m ≤ primitiveTrace p' m := by
  unfold primitiveTrace
  apply Finset.sum_le_sum
  intros n _
  exact Nat.mul_le_mul_left n (hp n)

/-- Primitive trace of the zero function is `0`.
    prop:time-space-commuting-diagram -/
theorem primitiveTrace_zero_fn (m : ℕ) :
    primitiveTrace (fun _ => 0) m = 0 := by
  unfold primitiveTrace
  simp

/-- Paper package: time/space commuting diagram primitive decomposition.
    prop:time-space-commuting-diagram -/
theorem paper_time_space_commuting_diagram :
    (∀ p : ℕ → ℕ, primitiveTrace p 0 = 0) ∧
    (∀ p : ℕ → ℕ, primitiveTrace p 1 = p 1) ∧
    (∀ (p : ℕ → ℕ) (q : ℕ), Nat.Prime q →
      primitiveTrace p q = p 1 + q * p q) ∧
    (∀ (p p' : ℕ → ℕ) (m : ℕ), (∀ n, p n ≤ p' n) →
      primitiveTrace p m ≤ primitiveTrace p' m) ∧
    (∀ m : ℕ, primitiveTrace (fun _ => 0) m = 0) :=
  ⟨primitiveTrace_zero,
   primitiveTrace_one,
   primitiveTrace_prime,
   primitiveTrace_mono,
   primitiveTrace_zero_fn⟩

end Omega.EA
