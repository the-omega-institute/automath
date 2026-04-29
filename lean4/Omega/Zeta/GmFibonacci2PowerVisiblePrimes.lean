import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Zeta.GmFibonacciSubtowerEntrypointCriterion

namespace Omega.Zeta

private lemma gmFibonacciEntrypoint_le_of_dvd_fib {m j : ℕ} (hm : 0 < m) (hj : 0 < j)
    (hdiv : m ∣ Nat.fib j) : gmFibonacciEntrypoint m ≤ j := by
  unfold gmFibonacciEntrypoint
  rw [dif_pos hm]
  exact Nat.find_min' (exists_gmFibonacciEntrypoint m hm) ⟨hj, hdiv⟩

private lemma gmFibonacciEntrypoint_minimal {m j : ℕ} (hm : 0 < m) (hj : 1 ≤ j)
    (hjlt : j < gmFibonacciEntrypoint m) : ¬ m ∣ Nat.fib j := by
  intro hdiv
  exact Nat.not_lt_of_ge (gmFibonacciEntrypoint_le_of_dvd_fib hm hj hdiv) hjlt

private lemma not_dvd_eight_two_pow_add_two (k : ℕ) : ¬ 8 ∣ 2 ^ k + 2 := by
  intro h
  by_cases hk : k < 3
  · interval_cases k <;> norm_num at h
  · have hk3 : 3 ≤ k := Nat.le_of_not_lt hk
    have hpow : 8 ∣ 2 ^ k := by
      simpa using (pow_dvd_pow 2 hk3 : 2 ^ 3 ∣ 2 ^ k)
    rcases h with ⟨a, ha⟩
    rcases hpow with ⟨b, hb⟩
    omega

/-- Paper label: `prop:gm-fibonacci-2power-visible-primes`. -/
theorem paper_gm_fibonacci_2power_visible_primes {p : ℕ} (hp : Nat.Prime p) :
    ((∃ k : ℕ, p ∣ Nat.fib (2 ^ k)) ↔ ∃ t : ℕ, Omega.Zeta.gmFibonacciEntrypoint p = 2 ^ t) ∧
      ¬ Omega.Zeta.GmFibonacciSubtowerCofinal (fun k => 2 ^ k) := by
  have hp_pos : 0 < p := hp.pos
  have hentry_pos : 1 ≤ gmFibonacciEntrypoint p :=
    Nat.succ_le_of_lt (gmFibonacciEntrypoint_pos hp_pos)
  have hentry : p ∣ Nat.fib (gmFibonacciEntrypoint p) :=
    gmFibonacciEntrypoint_dvd_fib hp_pos
  have hmin : ∀ j, 1 ≤ j → j < gmFibonacciEntrypoint p → ¬ p ∣ Nat.fib j := by
    intro j hj hjlt
    exact gmFibonacciEntrypoint_minimal hp_pos hj hjlt
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨k, hk⟩
      have hentry_iff :
          p ∣ Nat.fib (2 ^ k) ↔ gmFibonacciEntrypoint p ∣ 2 ^ k :=
        Omega.fib_prime_entry_point p (gmFibonacciEntrypoint p) (2 ^ k) hp hentry_pos hentry hmin
      have hpow : gmFibonacciEntrypoint p ∣ 2 ^ k := hentry_iff.mp hk
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 hpow with ⟨t, -, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simpa [ht] using hentry
  · intro hcofinal
    rcases hcofinal 7 (by norm_num) with ⟨k, hk⟩
    have h7 : 7 ∣ Nat.fib (2 ^ k + 2) := by
      simpa [foldCongruenceModulus] using hk
    have h8 : 8 ∣ 2 ^ k + 2 := (Omega.fib_seven_dvd_iff (2 ^ k + 2)).mp h7
    exact not_dvd_eight_two_pow_add_two k h8

end Omega.Zeta
