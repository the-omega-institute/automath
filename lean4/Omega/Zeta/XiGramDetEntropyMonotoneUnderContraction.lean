import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete scalar Gram package for a one-dimensional contraction model. The single vector has
positive norm, and the contraction factor lies in `(0, 1]`. -/
structure xi_gram_det_entropy_monotone_under_contraction_data where
  vectorNorm : ℝ
  contraction : ℝ
  vectorNorm_pos : 0 < vectorNorm
  contraction_pos : 0 < contraction
  contraction_le_one : contraction ≤ 1

/-- Determinant of the original one-dimensional Gram matrix. -/
def xi_gram_det_entropy_monotone_under_contraction_gram_det
    (D : xi_gram_det_entropy_monotone_under_contraction_data) : ℝ :=
  D.vectorNorm ^ 2

/-- Determinant of the contracted Gram matrix. -/
def xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det
    (D : xi_gram_det_entropy_monotone_under_contraction_data) : ℝ :=
  (D.contraction * D.vectorNorm) ^ 2

/-- Log-determinant entropy of the original Gram matrix. -/
noncomputable def xi_gram_det_entropy_monotone_under_contraction_gram_entropy
    (D : xi_gram_det_entropy_monotone_under_contraction_data) : ℝ :=
  Real.log (xi_gram_det_entropy_monotone_under_contraction_gram_det D)

/-- Log-determinant entropy of the contracted Gram matrix. -/
noncomputable def xi_gram_det_entropy_monotone_under_contraction_contracted_gram_entropy
    (D : xi_gram_det_entropy_monotone_under_contraction_data) : ℝ :=
  Real.log (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D)

/-- Quadratic form attached to the original Gram matrix. -/
def xi_gram_det_entropy_monotone_under_contraction_quadratic_form
    (D : xi_gram_det_entropy_monotone_under_contraction_data) (a : ℝ) : ℝ :=
  a ^ 2 * xi_gram_det_entropy_monotone_under_contraction_gram_det D

/-- Quadratic form attached to the contracted Gram matrix. -/
def xi_gram_det_entropy_monotone_under_contraction_contracted_quadratic_form
    (D : xi_gram_det_entropy_monotone_under_contraction_data) (a : ℝ) : ℝ :=
  a ^ 2 * xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D

/-- Equality means the contraction preserves the norm on the span of the distinguished vector. -/
def xi_gram_det_entropy_monotone_under_contraction_norm_preserving_on_span
    (D : xi_gram_det_entropy_monotone_under_contraction_data) : Prop :=
  D.contraction = 1

/-- Concrete paper-facing formulation of determinant and entropy monotonicity under contraction. -/
def xi_gram_det_entropy_monotone_under_contraction_statement
    (D : xi_gram_det_entropy_monotone_under_contraction_data) : Prop :=
  (∀ a,
      xi_gram_det_entropy_monotone_under_contraction_contracted_quadratic_form D a ≤
        xi_gram_det_entropy_monotone_under_contraction_quadratic_form D a) ∧
    xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D ≤
      xi_gram_det_entropy_monotone_under_contraction_gram_det D ∧
    xi_gram_det_entropy_monotone_under_contraction_contracted_gram_entropy D ≤
      xi_gram_det_entropy_monotone_under_contraction_gram_entropy D ∧
    (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D =
        xi_gram_det_entropy_monotone_under_contraction_gram_det D ↔
      xi_gram_det_entropy_monotone_under_contraction_norm_preserving_on_span D) ∧
    (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_entropy D =
        xi_gram_det_entropy_monotone_under_contraction_gram_entropy D ↔
      xi_gram_det_entropy_monotone_under_contraction_norm_preserving_on_span D)

private lemma xi_gram_det_entropy_monotone_under_contraction_contracted_det_le
    (D : xi_gram_det_entropy_monotone_under_contraction_data) :
    xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D ≤
      xi_gram_det_entropy_monotone_under_contraction_gram_det D := by
  have hsq : D.contraction ^ 2 ≤ 1 := by
    nlinarith [D.contraction_pos, D.contraction_le_one]
  have hnorm_nonneg : 0 ≤ D.vectorNorm ^ 2 := sq_nonneg D.vectorNorm
  calc
    xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D =
        D.contraction ^ 2 * D.vectorNorm ^ 2 := by
          dsimp [xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det]
          ring
    _ ≤ 1 * D.vectorNorm ^ 2 := by
      gcongr
    _ = xi_gram_det_entropy_monotone_under_contraction_gram_det D := by
      dsimp [xi_gram_det_entropy_monotone_under_contraction_gram_det]
      ring

private lemma xi_gram_det_entropy_monotone_under_contraction_gram_det_pos
    (D : xi_gram_det_entropy_monotone_under_contraction_data) :
    0 < xi_gram_det_entropy_monotone_under_contraction_gram_det D := by
  have hne : D.vectorNorm ≠ 0 := ne_of_gt D.vectorNorm_pos
  dsimp [xi_gram_det_entropy_monotone_under_contraction_gram_det]
  exact sq_pos_of_ne_zero hne

private lemma xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det_pos
    (D : xi_gram_det_entropy_monotone_under_contraction_data) :
    0 < xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D := by
  have hne : D.contraction * D.vectorNorm ≠ 0 :=
    mul_ne_zero (ne_of_gt D.contraction_pos) (ne_of_gt D.vectorNorm_pos)
  dsimp [xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det]
  exact sq_pos_of_ne_zero hne

private lemma xi_gram_det_entropy_monotone_under_contraction_det_eq_iff_norm_preserving
    (D : xi_gram_det_entropy_monotone_under_contraction_data) :
    (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D =
        xi_gram_det_entropy_monotone_under_contraction_gram_det D ↔
      xi_gram_det_entropy_monotone_under_contraction_norm_preserving_on_span D) := by
  constructor
  · intro hEq
    have hnorm_sq_ne : D.vectorNorm ^ 2 ≠ 0 := by
      exact ne_of_gt (sq_pos_of_ne_zero (ne_of_gt D.vectorNorm_pos))
    have hsq : D.contraction ^ 2 = 1 := by
      have hEq' : D.contraction ^ 2 * D.vectorNorm ^ 2 = D.vectorNorm ^ 2 := by
        calc
          D.contraction ^ 2 * D.vectorNorm ^ 2 = (D.contraction * D.vectorNorm) ^ 2 := by ring
          _ = D.vectorNorm ^ 2 := by
            simpa [xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det,
              xi_gram_det_entropy_monotone_under_contraction_gram_det] using hEq
      have hEq'' : D.contraction ^ 2 * D.vectorNorm ^ 2 = 1 * D.vectorNorm ^ 2 := by
        simpa using hEq'
      exact mul_right_cancel₀ hnorm_sq_ne hEq''
    have hc : D.contraction = 1 := by
      nlinarith [D.contraction_pos, D.contraction_le_one, hsq]
    exact hc
  · intro hPres
    dsimp [xi_gram_det_entropy_monotone_under_contraction_norm_preserving_on_span] at hPres
    dsimp [xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det,
      xi_gram_det_entropy_monotone_under_contraction_gram_det]
    simp [hPres]

private lemma xi_gram_det_entropy_monotone_under_contraction_entropy_eq_iff_norm_preserving
    (D : xi_gram_det_entropy_monotone_under_contraction_data) :
    (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_entropy D =
        xi_gram_det_entropy_monotone_under_contraction_gram_entropy D ↔
      xi_gram_det_entropy_monotone_under_contraction_norm_preserving_on_span D) := by
  constructor
  · intro hEq
    have hdet_le := xi_gram_det_entropy_monotone_under_contraction_contracted_det_le D
    have hgram_pos := xi_gram_det_entropy_monotone_under_contraction_gram_det_pos D
    have hcontracted_pos :=
      xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det_pos D
    have hdet_ge :
        xi_gram_det_entropy_monotone_under_contraction_gram_det D ≤
          xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D := by
      have hEq' :
          Real.log
              (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D) =
            Real.log (xi_gram_det_entropy_monotone_under_contraction_gram_det D) := by
        simpa [xi_gram_det_entropy_monotone_under_contraction_contracted_gram_entropy,
          xi_gram_det_entropy_monotone_under_contraction_gram_entropy] using hEq
      have hlog_ge :
          Real.log (xi_gram_det_entropy_monotone_under_contraction_gram_det D) ≤
            Real.log
              (xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det D) := by
        rw [hEq']
      exact (Real.log_le_log_iff hgram_pos hcontracted_pos).mp hlog_ge
    exact
      (xi_gram_det_entropy_monotone_under_contraction_det_eq_iff_norm_preserving D).mp
        (le_antisymm hdet_le hdet_ge)
  · intro hPres
    have hdet_eq :=
      (xi_gram_det_entropy_monotone_under_contraction_det_eq_iff_norm_preserving D).mpr hPres
    unfold xi_gram_det_entropy_monotone_under_contraction_contracted_gram_entropy
      xi_gram_det_entropy_monotone_under_contraction_gram_entropy
    simp [hdet_eq]

/-- Paper label: `prop:xi-gram-det-entropy-monotone-under-contraction`. In the one-dimensional
Gram model, the contraction shrinks every quadratic form, hence the Gram determinant and its
logarithm are monotone; equality holds exactly when the contraction is norm-preserving on the span
of the vector. -/
theorem paper_xi_gram_det_entropy_monotone_under_contraction
    (D : xi_gram_det_entropy_monotone_under_contraction_data) :
    xi_gram_det_entropy_monotone_under_contraction_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    dsimp [xi_gram_det_entropy_monotone_under_contraction_contracted_quadratic_form,
      xi_gram_det_entropy_monotone_under_contraction_quadratic_form]
    have hdet_le := xi_gram_det_entropy_monotone_under_contraction_contracted_det_le D
    nlinarith [sq_nonneg a, hdet_le]
  · exact xi_gram_det_entropy_monotone_under_contraction_contracted_det_le D
  · have hcontracted_pos :=
      xi_gram_det_entropy_monotone_under_contraction_contracted_gram_det_pos D
    exact Real.log_le_log hcontracted_pos
      (xi_gram_det_entropy_monotone_under_contraction_contracted_det_le D)
  · exact xi_gram_det_entropy_monotone_under_contraction_det_eq_iff_norm_preserving D
  · exact xi_gram_det_entropy_monotone_under_contraction_entropy_eq_iff_norm_preserving D

end Omega.Zeta
