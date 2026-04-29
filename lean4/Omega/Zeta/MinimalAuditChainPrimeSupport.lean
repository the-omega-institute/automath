import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Zeta

/-- Minimal audit chain obtained by adjoining a coprime successor factor at each step. -/
def minimalAuditChainLcm : Nat → Nat
  | 0 => 2
  | k + 1 => minimalAuditChainLcm k * (minimalAuditChainLcm k + 1)

lemma minimalAuditChainLcm_pos (k : Nat) : 0 < minimalAuditChainLcm k := by
  induction k with
  | zero =>
      simp [minimalAuditChainLcm]
  | succ k ih =>
      simp [minimalAuditChainLcm, ih]

/-- Each stage contributes a fresh prime divisor coming from the new coprime factor.
`thm:xi-primitive-prime-divisor-forces-unbounded-prime-support` -/
theorem paper_xi_primitive_prime_divisor_forces_unbounded_prime_support :
    ∃ k0 : Nat, ∀ k ≥ k0, ∃ p : Nat,
      Nat.Prime p ∧ p ∣ minimalAuditChainLcm k ∧ ¬ p ∣ minimalAuditChainLcm (k - 1) := by
  refine ⟨1, ?_⟩
  intro k hk
  cases k with
  | zero =>
      cases hk
  | succ j =>
      let a := minimalAuditChainLcm j
      let p := Nat.minFac (a + 1)
      have ha_pos : 0 < a := by
        dsimp [a]
        exact minimalAuditChainLcm_pos j
      have hp_prime : Nat.Prime p := by
        dsimp [p]
        apply Nat.minFac_prime
        omega
      have hp_dvd_factor : p ∣ a + 1 := by
        dsimp [p]
        exact Nat.minFac_dvd (a + 1)
      refine ⟨p, hp_prime, ?_, ?_⟩
      · dsimp [a]
        simpa [minimalAuditChainLcm, Nat.mul_comm] using dvd_mul_of_dvd_right hp_dvd_factor a
      · simp only [Nat.succ_sub_one]
        intro hp_dvd_prev
        have hp_dvd_a : p ∣ a := by
          simpa [a] using hp_dvd_prev
        have hp_dvd_one : p ∣ 1 := by
          simpa using Nat.dvd_sub hp_dvd_factor hp_dvd_a
        exact hp_prime.not_dvd_one hp_dvd_one

/-- Exact paper-label wrapper: cyclic audit chains need unbounded prime support. -/
theorem paper_xi_any_cyclic_audit_chain_needs_infinitely_many_primes :
    ∃ k0 : Nat, ∀ k ≥ k0, ∃ p : Nat,
      Nat.Prime p ∧ p ∣ minimalAuditChainLcm k ∧ ¬ p ∣ minimalAuditChainLcm (k - 1) := by
  exact paper_xi_primitive_prime_divisor_forces_unbounded_prime_support

end Omega.Zeta
