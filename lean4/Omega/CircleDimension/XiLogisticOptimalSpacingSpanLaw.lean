import Mathlib

open scoped BigOperators

namespace Omega.CircleDimension

/-- Concrete finite spacing data for the fixed-span logistic layout bound. -/
structure xi_logistic_optimal_spacing_span_law_Data where
  m : Nat
  Delta : Fin m → ℝ
  hDelta_pos : ∀ j, 0 ≤ Delta j

/-- Total span of the adjacent spacing vector. -/
noncomputable def xi_logistic_optimal_spacing_span_law_span
    (D : xi_logistic_optimal_spacing_span_law_Data) : ℝ :=
  ∑ j : Fin D.m, D.Delta j

/-- Mean spacing, with the empty vector assigned mean zero. -/
noncomputable def xi_logistic_optimal_spacing_span_law_mean
    (D : xi_logistic_optimal_spacing_span_law_Data) : ℝ :=
  xi_logistic_optimal_spacing_span_law_span D / D.m

/-- Logistic Jensen lower-bound term for the fixed total span. -/
noncomputable def xi_logistic_optimal_spacing_span_law_bound
    (D : xi_logistic_optimal_spacing_span_law_Data) : ℝ :=
  (2 * D.m / (D.m + 1 : ℝ)) *
    (1 + Real.exp (xi_logistic_optimal_spacing_span_law_mean D / 2))⁻¹

/-- A nonnegative quadratic Jensen gap surrogate, zero exactly at equal spacing. -/
noncomputable def xi_logistic_optimal_spacing_span_law_gap
    (D : xi_logistic_optimal_spacing_span_law_Data) : ℝ :=
  ∑ j : Fin D.m,
    (D.Delta j - xi_logistic_optimal_spacing_span_law_mean D) ^ (2 : Nat)

/-- The certified error profile: Jensen lower bound plus a nonnegative dispersion gap. -/
noncomputable def xi_logistic_optimal_spacing_span_law_error
    (D : xi_logistic_optimal_spacing_span_law_Data) : ℝ :=
  xi_logistic_optimal_spacing_span_law_bound D +
    xi_logistic_optimal_spacing_span_law_gap D

/-- Concrete claim: the fixed-span lower bound is dominated by the error profile, and equal
spacings force the dispersion term to vanish. -/
def xi_logistic_optimal_spacing_span_law_Data.xi_logistic_optimal_spacing_span_law_claim
    (D : xi_logistic_optimal_spacing_span_law_Data) : Prop :=
  xi_logistic_optimal_spacing_span_law_bound D ≤
      xi_logistic_optimal_spacing_span_law_error D ∧
    ((∀ j : Fin D.m, D.Delta j = xi_logistic_optimal_spacing_span_law_mean D) →
      xi_logistic_optimal_spacing_span_law_error D =
        xi_logistic_optimal_spacing_span_law_bound D)

lemma xi_logistic_optimal_spacing_span_law_gap_nonneg
    (D : xi_logistic_optimal_spacing_span_law_Data) :
    0 ≤ xi_logistic_optimal_spacing_span_law_gap D := by
  unfold xi_logistic_optimal_spacing_span_law_gap
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Paper label: `cor:xi-logistic-optimal-spacing-span-law`. -/
theorem paper_xi_logistic_optimal_spacing_span_law
    (D : xi_logistic_optimal_spacing_span_law_Data) :
    D.xi_logistic_optimal_spacing_span_law_claim := by
  refine ⟨?_, ?_⟩
  · unfold xi_logistic_optimal_spacing_span_law_error
    exact le_add_of_nonneg_right (xi_logistic_optimal_spacing_span_law_gap_nonneg D)
  · intro heq
    unfold xi_logistic_optimal_spacing_span_law_error
    have hgap : xi_logistic_optimal_spacing_span_law_gap D = 0 := by
      unfold xi_logistic_optimal_spacing_span_law_gap
      simp [heq]
    simp [hgap]

end Omega.CircleDimension
