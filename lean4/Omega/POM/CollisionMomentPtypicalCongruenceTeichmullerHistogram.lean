import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.NumberTheory.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Scalar prime-power Frobenius congruence for natural powers. -/
lemma pom_collision_moment_ptypical_congruence_teichmuller_histogram_scalar
    (p a : ℕ) (hp : Nat.Prime p) :
    ∀ k : ℕ, 1 ≤ k → Nat.ModEq (p ^ k) (a ^ (p ^ k)) (a ^ (p ^ (k - 1))) := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  have hfermat : ((p : ℤ) ∣ (a : ℤ) ^ p - (a : ℤ)) :=
    Int.prime_dvd_pow_self_sub hp (a : ℤ)
  have hdiv :
      ((p : ℤ) ^ (j + 1) ∣
        ((a : ℤ) ^ p) ^ p ^ j - (a : ℤ) ^ p ^ j) :=
    dvd_sub_pow_of_dvd_sub (R := ℤ) hfermat j
  rw [Nat.modEq_iff_dvd]
  convert hdiv.neg_right using 1
  simp [pow_mul, pow_succ, mul_comm]

/-- Paper label: `prop:pom-collision-moment-ptypical-congruence-teichmuller-histogram`. -/
theorem paper_pom_collision_moment_ptypical_congruence_teichmuller_histogram
    (p m : ℕ) (hp : Nat.Prime p) (d : Fin m → ℕ) :
    ∀ k : ℕ, 1 ≤ k →
      Nat.ModEq (p ^ k) (∑ x : Fin m, d x ^ (p ^ k))
        (∑ x : Fin m, d x ^ (p ^ (k - 1))) := by
  intro k hk
  exact Nat.ModEq.sum (fun x _ =>
    pom_collision_moment_ptypical_congruence_teichmuller_histogram_scalar p (d x) hp k hk)

end Omega.POM
