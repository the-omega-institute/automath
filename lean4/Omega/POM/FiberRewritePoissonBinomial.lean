import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

open Finset

/-- Rewriting the normalized generating polynomial as a Poisson-binomial product by setting
`p_j = (1 + α_j)⁻¹`. The product, mean, and variance identities are then finite-sum algebra. -/
theorem paper_pom_fiber_rewrite_poisson_binomial (d : ℕ) (alpha : Fin d → ℝ)
    (halpha : ∀ j, 0 < alpha j) :
    ∃ p : Fin d → ℝ,
      (∀ j, 0 < p j ∧ p j < 1) ∧
      (∀ t : ℝ, (∏ j : Fin d, ((alpha j + t) / (alpha j + 1))) = ∏ j : Fin d, (1 - p j + p j * t)) ∧
      (∑ j : Fin d, p j = ∑ j : Fin d, (1 / (1 + alpha j))) ∧
      (∑ j : Fin d, p j * (1 - p j) = ∑ j : Fin d, (alpha j / (1 + alpha j) ^ 2)) := by
  refine ⟨fun j => 1 / (1 + alpha j), ?_, ?_, ?_, ?_⟩
  · intro j
    constructor
    · have hden : 0 < 1 + alpha j := by linarith [halpha j]
      positivity
    · have hden : 0 < 1 + alpha j := by linarith [halpha j]
      field_simp [hden.ne']
      linarith [halpha j]
  · intro t
    apply Finset.prod_congr rfl
    intro j hj
    have hden : (1 + alpha j : ℝ) ≠ 0 := by linarith [halpha j]
    have hden' : (alpha j + 1 : ℝ) ≠ 0 := by simpa [add_comm] using hden
    apply (div_eq_iff hden').2
    field_simp [hden]
    ring
  · rfl
  · apply Finset.sum_congr rfl
    intro j hj
    have hden : (1 + alpha j : ℝ) ≠ 0 := by linarith [halpha j]
    field_simp [hden]
    ring_nf

end Omega.POM
