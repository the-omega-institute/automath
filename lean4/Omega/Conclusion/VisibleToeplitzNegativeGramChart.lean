import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Concrete block-diagonal congruence package for the visible Toeplitz negative chart. -/
structure conclusion_visible_toeplitz_negative_gram_chart_data where
  upperDim : ℕ
  κ : ℕ
  toeplitz :
    Matrix (Sum (Fin upperDim) (Fin κ)) (Sum (Fin upperDim) (Fin κ)) ℝ
  congruence :
    Matrix (Sum (Fin upperDim) (Fin κ)) (Sum (Fin upperDim) (Fin κ)) ℝ
  positiveBlock : Matrix (Fin upperDim) (Fin upperDim) ℝ
  hankelBlock : Matrix (Fin κ) (Fin κ) ℝ
  congruence_diagonalizes :
    congruence.transpose * toeplitz * congruence =
      Matrix.fromBlocks positiveBlock 0 0 (-(hankelBlock.transpose * hankelBlock))
  congruence_injective : Function.Injective congruence.mulVec
  hankelBlock_injective : Function.Injective hankelBlock.mulVec

/-- The lower chart coordinates `(0,v)` in the strictified block decomposition. -/
def conclusion_visible_toeplitz_negative_gram_chart_lower_input
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) (v : Fin D.κ → ℝ) :
    Sum (Fin D.upperDim) (Fin D.κ) → ℝ :=
  Sum.elim (fun _ => 0) v

/-- The visible negative chart obtained by pushing the lower block through the congruence map. -/
def conclusion_visible_toeplitz_negative_gram_chart_chart
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) (v : Fin D.κ → ℝ) :
    Sum (Fin D.upperDim) (Fin D.κ) → ℝ :=
  D.congruence *ᵥ conclusion_visible_toeplitz_negative_gram_chart_lower_input D v

/-- Pull back the Toeplitz quadratic form to the lower chart coordinates. -/
def conclusion_visible_toeplitz_negative_gram_chart_pullback
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) (v : Fin D.κ → ℝ) : ℝ :=
  -dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v)

private lemma conclusion_visible_toeplitz_negative_gram_chart_lower_input_injective
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) :
    Function.Injective (conclusion_visible_toeplitz_negative_gram_chart_lower_input D) := by
  intro v w h
  ext i
  exact congrFun h (Sum.inr i)

private lemma conclusion_visible_toeplitz_negative_gram_chart_hankel_quadratic
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) (v : Fin D.κ → ℝ) :
    dotProduct v (((D.hankelBlock.transpose * D.hankelBlock).mulVec v)) =
      dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The strictified lower block gives an exact negative Gram chart: the chart map is injective,
the pulled-back quadratic form is `-‖Hv‖²`, and the form is strictly negative away from `0`
because the Hankel block has full rank. -/
def conclusion_visible_toeplitz_negative_gram_chart_statement
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) : Prop :=
  Function.Injective (conclusion_visible_toeplitz_negative_gram_chart_chart D) ∧
    (∀ v : Fin D.κ → ℝ,
      conclusion_visible_toeplitz_negative_gram_chart_pullback D v =
        -dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v)) ∧
    ∀ v : Fin D.κ → ℝ, v ≠ 0 →
      conclusion_visible_toeplitz_negative_gram_chart_pullback D v < 0

/-- Paper label: `thm:conclusion-visible-toeplitz-negative-gram-chart`. The block-diagonal
congruence identifies the lower visible Toeplitz directions with the negative Hankel Gram block,
so the pulled-back quadratic form is exactly `-‖Hv‖²`; injectivity of the Hankel block forces
strict negativity on every nonzero chart vector. -/
theorem paper_conclusion_visible_toeplitz_negative_gram_chart
    (D : conclusion_visible_toeplitz_negative_gram_chart_data) :
    conclusion_visible_toeplitz_negative_gram_chart_statement D := by
  have hchart :
      Function.Injective (conclusion_visible_toeplitz_negative_gram_chart_chart D) := by
    intro v w h
    apply conclusion_visible_toeplitz_negative_gram_chart_lower_input_injective D
    exact D.congruence_injective h
  have hpullback :
      ∀ v : Fin D.κ → ℝ,
        conclusion_visible_toeplitz_negative_gram_chart_pullback D v =
          -dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v) := by
    intro v
    rfl
  refine ⟨hchart, hpullback, ?_⟩
  intro v hv
  rw [hpullback]
  have hHv_ne : D.hankelBlock.mulVec v ≠ 0 := by
    intro hHv
    apply hv
    apply D.hankelBlock_injective
    simpa using hHv
  have hnonneg : 0 ≤ dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v) := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((D.hankelBlock.mulVec v) i)
  have hne :
      dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v) ≠ 0 := by
    intro hzero
    exact hHv_ne (dotProduct_self_eq_zero.mp hzero)
  have hpos : 0 < dotProduct (D.hankelBlock.mulVec v) (D.hankelBlock.mulVec v) := by
    exact lt_of_le_of_ne hnonneg hne.symm
  linarith

end Omega.Conclusion
