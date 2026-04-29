import Mathlib.Tactic

namespace Omega.Zeta

/-- Every divisor of `p^a` is a power `p^j` with `j ≤ a`. -/
def xi_visible_arithmetic_primepower_quotient_chain_divisor_power_clause
    (p a : ℕ) : Prop :=
  ∀ d ∈ Nat.divisors (p ^ a), ∃ j ≤ a, d = p ^ j

/-- Every listed power `p^j`, `j ≤ a`, occurs as a divisor of `p^a`. -/
def xi_visible_arithmetic_primepower_quotient_chain_power_divisor_clause
    (p a : ℕ) : Prop :=
  ∀ j ≤ a, p ^ j ∈ Nat.divisors (p ^ a)

/-- Divisors in the prime-power list are linearly ordered by divisibility. -/
def xi_visible_arithmetic_primepower_quotient_chain_linear_clause
    (p a : ℕ) : Prop :=
  ∀ i j, i ≤ a → j ≤ a → p ^ i ∣ p ^ j ∨ p ^ j ∣ p ^ i

/-- The prime-power divisor lattice has exactly `a + 1` nodes. -/
def xi_visible_arithmetic_primepower_quotient_chain_card_clause
    (p a : ℕ) : Prop :=
  (Nat.divisors (p ^ a)).card = a + 1

/-- Paper-facing prime-power quotient-chain certificate. -/
def xi_visible_arithmetic_primepower_quotient_chain_statement
    (p a : ℕ) : Prop :=
  xi_visible_arithmetic_primepower_quotient_chain_divisor_power_clause p a ∧
    xi_visible_arithmetic_primepower_quotient_chain_power_divisor_clause p a ∧
      xi_visible_arithmetic_primepower_quotient_chain_linear_clause p a ∧
        xi_visible_arithmetic_primepower_quotient_chain_card_clause p a

/-- Paper label: `cor:xi-visible-arithmetic-primepower-quotient-chain`. -/
theorem paper_xi_visible_arithmetic_primepower_quotient_chain {p a : ℕ}
    (hp : Nat.Prime p) :
    xi_visible_arithmetic_primepower_quotient_chain_statement p a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    exact (Nat.mem_divisors_prime_pow hp a).mp hd
  · intro j hj
    exact (Nat.mem_divisors_prime_pow hp a).mpr ⟨j, hj, rfl⟩
  · intro i j _hi _hj
    rcases le_total i j with hij | hji
    · exact Or.inl (pow_dvd_pow p hij)
    · exact Or.inr (pow_dvd_pow p hji)
  · unfold xi_visible_arithmetic_primepower_quotient_chain_card_clause
    rw [Nat.divisors_prime_pow hp a]
    simp

end Omega.Zeta
