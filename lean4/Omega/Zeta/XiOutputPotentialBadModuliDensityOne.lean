import Mathlib.Tactic
import Omega.Zeta.XiOutputPotentialLargeOddPrimesBad

namespace Omega.Zeta

/-- Concrete data for the density-one bad-moduli consequence.  `OddPrime` is kept as the
paper-facing predicate used by the large-prime theorem, with a bridge to `Nat.Prime` and `p ≠ 2`;
`bad_divisibility_upward` records the divisibility monotonicity input. -/
structure xi_output_potential_bad_moduli_density_one_data where
  Bad : ℕ → Prop
  OddPrime : ℕ → Prop
  theta : ℕ → ℝ
  thetaOne : ℕ → ℝ
  oddPrime_iff : ∀ p, OddPrime p ↔ Nat.Prime p ∧ p ≠ 2
  eventually_thetaOne_half :
    ∃ p0, ∀ p, p0 ≤ p → OddPrime p → (1 / 2 : ℝ) < thetaOne p
  thetaOne_le_theta : ∀ p, OddPrime p → thetaOne p ≤ theta p
  theta_bad : ∀ p, OddPrime p → (1 / 2 : ℝ) < theta p → Bad p
  bad_divisibility_upward : ∀ {m n : ℕ}, Bad m → m ∣ n → Bad n

/-- The bad set contains every sufficiently large odd prime, and any non-bad integer has all
prime divisors in the finite exceptional set `{2} ∪ {p < p₀}`. -/
def xi_output_potential_bad_moduli_density_one_statement
    (D : xi_output_potential_bad_moduli_density_one_data) : Prop :=
  ∃ p0 : ℕ,
    (∀ p : ℕ, p0 ≤ p → Nat.Prime p → p ≠ 2 → D.Bad p) ∧
      ∀ n : ℕ, 2 ≤ n → ¬ D.Bad n →
        ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 2 ∨ p < p0

/-- Paper label: `cor:xi-output-potential-bad-moduli-density-one`. -/
theorem paper_xi_output_potential_bad_moduli_density_one
    (D : xi_output_potential_bad_moduli_density_one_data) :
    xi_output_potential_bad_moduli_density_one_statement D := by
  rcases paper_xi_output_potential_large_odd_primes_bad D.OddPrime D.Bad D.theta D.thetaOne
      D.eventually_thetaOne_half D.thetaOne_le_theta D.theta_bad with
    ⟨p0, hp0⟩
  refine ⟨p0, ?_, ?_⟩
  · intro p hp_ge hp_prime hp_ne_two
    exact hp0 p hp_ge ((D.oddPrime_iff p).mpr ⟨hp_prime, hp_ne_two⟩)
  · intro n _hn hnot_bad p hp_prime hp_dvd
    by_cases hp_two : p = 2
    · exact Or.inl hp_two
    · refine Or.inr (lt_of_not_ge ?_)
      intro hp_ge
      have hp_odd : D.OddPrime p := (D.oddPrime_iff p).mpr ⟨hp_prime, hp_two⟩
      have hp_bad : D.Bad p := hp0 p hp_ge hp_odd
      exact hnot_bad (D.bad_divisibility_upward hp_bad hp_dvd)

end Omega.Zeta
