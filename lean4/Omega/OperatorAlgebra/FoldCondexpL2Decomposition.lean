import Omega.OperatorAlgebra.FoldConditionalExpectation
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

namespace Omega.OperatorAlgebra

open FoldConditionalExpectationData

namespace FoldConditionalExpectationData

lemma fold_condexp_l2_decomposition_sum_fiberwise
    (D : FoldConditionalExpectationData) (g : D.Ω → ℚ) :
    (∑ a : D.Ω, g a) = ∑ x : D.X, ∑ a ∈ D.fiber x, g a := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := D.fold) (f := g)]
  simp [fiber]

lemma fold_condexp_l2_decomposition_fiber_contraction
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) (x : D.X) :
    (∑ a ∈ D.fiber x, (D.foldExpectation f a) ^ 2) ≤
      ∑ a ∈ D.fiber x, (f a) ^ 2 := by
  classical
  set S : ℚ := ∑ a ∈ D.fiber x, f a
  set n : ℚ := (D.fiberCard x : ℚ)
  have hn_pos : 0 < n := by
    simpa [n] using (show (0 : ℚ) < (D.fiberCard x : ℚ) by
      exact_mod_cast D.fiberCard_pos x)
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hsq : S ^ 2 ≤ n * ∑ a ∈ D.fiber x, (f a) ^ 2 := by
    simpa [S, n, fiberCard] using
      (sq_sum_le_card_mul_sum_sq (s := D.fiber x) (f := f))
  have hconst :
      (∑ a ∈ D.fiber x, (D.foldExpectation f a) ^ 2) = S ^ 2 / n := by
    calc
      (∑ a ∈ D.fiber x, (D.foldExpectation f a) ^ 2)
          = ∑ a ∈ D.fiber x, (S / n) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              have hfold : D.fold a = x := by
                simpa [fiber] using ha
              simp [foldExpectation, S, n, hfold]
      _ = n * (S / n) ^ 2 := by
              simp [n, fiberCard]
      _ = S ^ 2 / n := by
              field_simp [hn_ne]
  rw [hconst]
  exact (div_le_iff₀ hn_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsq)

lemma fold_condexp_l2_decomposition_contraction
    (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    (∑ a : D.Ω, (D.foldExpectation f a) ^ 2) ≤ ∑ a : D.Ω, (f a) ^ 2 := by
  classical
  rw [D.fold_condexp_l2_decomposition_sum_fiberwise (fun a => (D.foldExpectation f a) ^ 2),
    D.fold_condexp_l2_decomposition_sum_fiberwise (fun a => (f a) ^ 2)]
  exact Finset.sum_le_sum fun x _hx =>
    D.fold_condexp_l2_decomposition_fiber_contraction f x

end FoldConditionalExpectationData

/-- prop:fold-condexp-l2-decomposition -/
theorem paper_fold_condexp_l2_decomposition (D : FoldConditionalExpectationData) :
    (∀ f : D.Ω → ℚ, D.foldExpectation (D.foldExpectation f) = D.foldExpectation f) ∧
      (∀ f : D.Ω → ℚ,
        (∑ a : D.Ω, (D.foldExpectation f a) ^ 2) ≤ (∑ a : D.Ω, (f a) ^ 2)) := by
  exact ⟨fun f => D.foldExpectation_idempotent f,
    fun f => D.fold_condexp_l2_decomposition_contraction f⟩

end Omega.OperatorAlgebra
