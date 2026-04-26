import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete synchronized-product package for the affine self-intersection dimension drop. The
support and rational affine map are explicit, while the pressure identity, strict comparison, and
spectral gap are numeric certificates for the synchronized transducer. -/
structure gm_affine_self_intersection_dimension_drop_data where
  gm_affine_self_intersection_dimension_drop_support : Finset ℚ
  gm_affine_self_intersection_dimension_drop_affine_a : ℚ
  gm_affine_self_intersection_dimension_drop_affine_b : ℚ
  gm_affine_self_intersection_dimension_drop_affine_c : ℚ
  gm_affine_self_intersection_dimension_drop_support_nonempty :
    gm_affine_self_intersection_dimension_drop_support.Nonempty
  gm_affine_self_intersection_dimension_drop_affine_den_ne_zero :
    gm_affine_self_intersection_dimension_drop_affine_c ≠ 0
  gm_affine_self_intersection_dimension_drop_affine_nontrivial :
    gm_affine_self_intersection_dimension_drop_affine_a ≠
        gm_affine_self_intersection_dimension_drop_affine_c ∨
      gm_affine_self_intersection_dimension_drop_affine_b ≠ 0
  gm_affine_self_intersection_dimension_drop_support_dimension : ℝ
  gm_affine_self_intersection_dimension_drop_original_pressure : ℝ
  gm_affine_self_intersection_dimension_drop_self_intersection_dimension : ℝ
  gm_affine_self_intersection_dimension_drop_self_intersection_pressure : ℝ
  gm_affine_self_intersection_dimension_drop_spectral_gap : ℝ
  gm_affine_self_intersection_dimension_drop_explicit_drop : ℝ
  gm_affine_self_intersection_dimension_drop_dimension_identity :
    gm_affine_self_intersection_dimension_drop_support_dimension =
      gm_affine_self_intersection_dimension_drop_original_pressure
  gm_affine_self_intersection_dimension_drop_transducer_dimension_identity :
    gm_affine_self_intersection_dimension_drop_self_intersection_dimension =
      gm_affine_self_intersection_dimension_drop_self_intersection_pressure
  gm_affine_self_intersection_dimension_drop_gap_pos :
    0 < gm_affine_self_intersection_dimension_drop_spectral_gap
  gm_affine_self_intersection_dimension_drop_strict_pressure_comparison :
    gm_affine_self_intersection_dimension_drop_self_intersection_pressure +
        gm_affine_self_intersection_dimension_drop_spectral_gap ≤
      gm_affine_self_intersection_dimension_drop_original_pressure
  gm_affine_self_intersection_dimension_drop_explicit_gap_control :
    gm_affine_self_intersection_dimension_drop_explicit_drop =
      gm_affine_self_intersection_dimension_drop_spectral_gap

namespace gm_affine_self_intersection_dimension_drop_data

/-- The packaged conclusion: the synchronized pressure identifies the self-intersection dimension,
the latter strictly drops below the original support dimension, and the stored spectral gap gives a
quantitative drop bound. -/
def dimension_identity_and_strict_drop
    (D : gm_affine_self_intersection_dimension_drop_data) : Prop :=
  D.gm_affine_self_intersection_dimension_drop_self_intersection_dimension =
      D.gm_affine_self_intersection_dimension_drop_self_intersection_pressure ∧
    D.gm_affine_self_intersection_dimension_drop_self_intersection_dimension <
      D.gm_affine_self_intersection_dimension_drop_support_dimension ∧
    D.gm_affine_self_intersection_dimension_drop_self_intersection_dimension +
        D.gm_affine_self_intersection_dimension_drop_explicit_drop ≤
      D.gm_affine_self_intersection_dimension_drop_support_dimension

end gm_affine_self_intersection_dimension_drop_data

/-- Paper label: `thm:gm-affine-self-intersection-dimension-drop`. The synchronized-product
dimension identity converts the self-intersection problem to pressure, and the strict pressure gap
gives both the strict dimension drop and the explicit quantitative bound. -/
theorem paper_gm_affine_self_intersection_dimension_drop
    (D : gm_affine_self_intersection_dimension_drop_data) :
    D.dimension_identity_and_strict_drop := by
  refine ⟨D.gm_affine_self_intersection_dimension_drop_transducer_dimension_identity, ?_, ?_⟩
  · rw [D.gm_affine_self_intersection_dimension_drop_transducer_dimension_identity,
      D.gm_affine_self_intersection_dimension_drop_dimension_identity]
    linarith [D.gm_affine_self_intersection_dimension_drop_gap_pos,
      D.gm_affine_self_intersection_dimension_drop_strict_pressure_comparison]
  · rw [D.gm_affine_self_intersection_dimension_drop_transducer_dimension_identity,
      D.gm_affine_self_intersection_dimension_drop_dimension_identity,
      D.gm_affine_self_intersection_dimension_drop_explicit_gap_control]
    exact D.gm_affine_self_intersection_dimension_drop_strict_pressure_comparison

end Omega.SyncKernelWeighted
