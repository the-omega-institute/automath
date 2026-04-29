import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.POM.FiberIndsetFactorization
import Omega.POM.FiberRewritePoissonBinomial

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `prop:pom-fiber-rewrite-independent-sum`.
The path-factorization identifies the fiber with a product of path independent-set families, and the
componentwise Lee--Yang rewrite turns the size statistic into a sum of independent Bernoulli
components with additive mean and variance. -/
theorem paper_pom_fiber_rewrite_independent_sum (lengths : List ℕ)
    (alpha : (i : Fin lengths.length) → Fin (lengths.get i) → ℝ)
    (halpha : ∀ i j, 0 < alpha i j) :
    Nonempty (((i : Fin lengths.length) → Omega.X (lengths.get i)) ≃
      ((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) ∧
      ∃ p : (i : Fin lengths.length) → Fin (lengths.get i) → ℝ,
        (∀ i j, 0 < p i j ∧ p i j < 1) ∧
        (∀ t : ℝ,
          (∏ i : Fin lengths.length,
              ∏ j : Fin (lengths.get i), ((alpha i j + t) / (alpha i j + 1))) =
            ∏ i : Fin lengths.length,
              ∏ j : Fin (lengths.get i), (1 - p i j + p i j * t)) ∧
        (∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), p i j =
          ∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), (1 / (1 + alpha i j))) ∧
        (∑ i : Fin lengths.length, ∑ j : Fin (lengths.get i), p i j * (1 - p i j) =
          ∑ i : Fin lengths.length,
            ∑ j : Fin (lengths.get i), (alpha i j / (1 + alpha i j) ^ 2)) := by
  rcases paper_pom_fiber_indset_factorization lengths with ⟨hequiv, -, -⟩
  refine ⟨hequiv, ?_⟩
  refine ⟨fun i j => 1 / (1 + alpha i j), ?_, ?_, rfl, ?_⟩
  · intro i j
    constructor
    · have hden : 0 < 1 + alpha i j := by linarith [halpha i j]
      positivity
    · have hden : 0 < 1 + alpha i j := by linarith [halpha i j]
      field_simp [hden.ne']
      linarith [halpha i j]
  · intro t
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    have hden : (1 + alpha i j : ℝ) ≠ 0 := by linarith [halpha i j]
    have hden' : (alpha i j + 1 : ℝ) ≠ 0 := by simpa [add_comm] using hden
    apply (div_eq_iff hden').2
    field_simp [hden]
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hden : (1 + alpha i j : ℝ) ≠ 0 := by linarith [halpha i j]
    field_simp [hden]
    ring_nf

end Omega.POM
