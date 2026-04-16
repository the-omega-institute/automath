import Mathlib

open scoped BigOperators

namespace Omega.POM.MultiplicativeChainRuleFinite

theorem paper_pom_multiplicative_chain_rule_finite_m_seeds
    {α : Type} [Fintype α] [DecidableEq α]
    (d : α → ℝ) (a b : ℕ) (hSa : (∑ x, d x ^ a) ≠ 0) :
    let S : ℕ → ℝ := fun q => ∑ x, d x ^ q
    let π : α → ℝ := fun x => d x ^ a / S a
    S (a * b) = S a ^ b * ∑ x, (π x) ^ b := by
  classical
  dsimp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [div_pow, ← pow_mul]
  field_simp [hSa]

theorem paper_pom_multiplicative_chain_rule_finite_m_package
    {α : Type} [Fintype α] [DecidableEq α]
    (d : α → ℝ) (a b : ℕ) (hSa : (∑ x, d x ^ a) ≠ 0) :
    let S : ℕ → ℝ := fun q => ∑ x, d x ^ q
    let π : α → ℝ := fun x => d x ^ a / S a
    S (a * b) = S a ^ b * ∑ x, (π x) ^ b :=
  paper_pom_multiplicative_chain_rule_finite_m_seeds d a b hSa

end Omega.POM.MultiplicativeChainRuleFinite
