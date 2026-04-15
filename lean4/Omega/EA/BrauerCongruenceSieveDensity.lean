import Mathlib.Tactic

namespace Omega.EA

/-- Single prime congruence density `1/2 = 1/2¹`.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem single_binary_density : (1 : ℚ) / 2 = 1 / 2 ^ 1 := by norm_num

/-- Two-prime congruence density `1/4 = 1/2²`.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem two_binary_density : (1 : ℚ) / 4 = 1 / 2 ^ 2 := by norm_num

/-- Three-prime congruence density `1/8 = 1/2³`.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem three_binary_density : (1 : ℚ) / 8 = 1 / 2 ^ 3 := by norm_num

/-- Independent binary densities multiply: `1/2ⁿ = (1/2)ⁿ`.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem independent_binary_density (n : ℕ) :
    (1 : ℚ) / (2 ^ n) = (1 / 2) ^ n := by
  rw [div_pow, one_pow]

/-- Reverse form: `(1/2)ⁿ = 1/2ⁿ`.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem neg_power_eq_reciprocal (n : ℕ) :
    ((1 : ℚ) / 2) ^ n = 1 / 2 ^ n := by
  rw [div_pow, one_pow]

/-- Multiplicative refinement: adding one prime halves the density.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem density_multiplicative (n : ℕ) :
    (1 : ℚ) / 2 ^ (n + 1) = ((1 : ℚ) / 2 ^ n) * (1 / 2) := by
  rw [pow_succ]
  field_simp

/-- Densities are strictly less than 1 from `n ≥ 1`.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem density_lt_one (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℚ) / 2 ^ n < 1 := by
  have h2pow : (1 : ℚ) < 2 ^ n := by
    have : (1 : ℚ) < 2 := by norm_num
    exact one_lt_pow₀ this (by omega)
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  rw [div_lt_one hpos]
  exact h2pow

/-- Paper package: Brauer congruence sieve density formulas.
    cor:prime-register-brauer-congruence-sieve-density -/
theorem paper_prime_register_brauer_congruence_sieve_density :
    (1 : ℚ) / 2 = 1 / 2 ^ 1 ∧
    (1 : ℚ) / 4 = 1 / 2 ^ 2 ∧
    (1 : ℚ) / 8 = 1 / 2 ^ 3 ∧
    (∀ n : ℕ, (1 : ℚ) / (2 ^ n) = (1 / 2) ^ n) ∧
    (∀ n : ℕ, ((1 : ℚ) / 2) ^ n = 1 / 2 ^ n) ∧
    (∀ n : ℕ, (1 : ℚ) / 2 ^ (n + 1) = ((1 : ℚ) / 2 ^ n) * (1 / 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (1 : ℚ) / 2 ^ n < 1) :=
  ⟨single_binary_density,
   two_binary_density,
   three_binary_density,
   independent_binary_density,
   neg_power_eq_reciprocal,
   density_multiplicative,
   density_lt_one⟩

end Omega.EA
