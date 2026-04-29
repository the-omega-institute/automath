import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Paper label: `thm:finite-uniform-layer-variance-dissipation`. -/
theorem paper_finite_uniform_layer_variance_dissipation (n : ℕ) (hn : 0 < n)
    (f : Fin n → ℝ) :
    (∑ _i : Fin n, ((∑ j : Fin n, f j) / (n : ℝ)) ^ 2) ≤
      ∑ i : Fin n, (f i) ^ 2 := by
  classical
  let S : ℝ := ∑ j : Fin n, f j
  let Q : ℝ := ∑ i : Fin n, (f i) ^ 2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcs : S ^ 2 ≤ (n : ℝ) * Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := f)
    simpa [S, Q, Finset.card_univ] using h
  have hdiv : S ^ 2 / (n : ℝ) ≤ Q := by
    rw [div_le_iff₀ hnR]
    nlinarith
  calc
    (∑ _i : Fin n, ((∑ j : Fin n, f j) / (n : ℝ)) ^ 2)
        = (n : ℝ) * (S / (n : ℝ)) ^ 2 := by
          simp [S, Finset.card_univ]
    _ = S ^ 2 / (n : ℝ) := by
          field_simp [ne_of_gt hnR]
    _ ≤ Q := hdiv
    _ = ∑ i : Fin n, (f i) ^ 2 := by
          simp [Q]

end Omega.OperatorAlgebra
