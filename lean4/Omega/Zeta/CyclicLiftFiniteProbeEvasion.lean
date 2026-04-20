import Mathlib.Tactic

namespace Omega.Zeta

/-- Any finite collection of modular obstructions can be avoided by infinitely many primes, so a
finite probe family excludes only finitely many lift orders.
    thm:zeta-cyclic-lift-finite-probe-evasion -/
theorem paper_zeta_cyclic_lift_finite_probe_evasion (S : Finset ℕ) :
    Set.Infinite {q : ℕ | Nat.Prime q ∧ ∀ n ∈ S, 2 ≤ n → q % n ≠ 0} := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨p, hp_bound, hp_prime⟩ := Nat.exists_infinite_primes (a + S.sum id + 1)
  have ha_lt_p : a < p := by omega
  refine ⟨p, ?_, ha_lt_p⟩
  refine ⟨hp_prime, ?_⟩
  intro n hn hn_two
  by_contra hmod
  have hdiv : n ∣ p := Nat.dvd_of_mod_eq_zero hmod
  have hcases : n = 1 ∨ n = p := (Nat.dvd_prime hp_prime).1 hdiv
  have hn_le_sum : n ≤ S.sum id := by
    simpa using Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hn
  have hn_lt_p : n < p := by
    calc
      n ≤ S.sum id := hn_le_sum
      _ < a + S.sum id + 1 := by omega
      _ ≤ p := hp_bound
  rcases hcases with h1 | hp
  · omega
  · omega

end Omega.Zeta
