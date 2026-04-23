import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete pairwise TV data for two frozen escort states compared through a common maximal-fiber
reference measure. The recorded half-envelope bounds are sufficient both for the triangle-inequality
estimate and for the single min-gap envelope. -/
structure xi_fixed_freezing_escort_pairwise_tv_coalescence_data where
  tvDistance : ℝ
  referenceDistanceA : ℝ
  referenceDistanceB : ℝ
  gapA : ℝ
  gapB : ℝ
  triangle_bound : tvDistance ≤ referenceDistanceA + referenceDistanceB
  referenceDistanceA_bound : referenceDistanceA ≤ (1 / 2 : ℝ) * Real.exp (-gapA)
  referenceDistanceB_bound : referenceDistanceB ≤ (1 / 2 : ℝ) * Real.exp (-gapB)

private lemma xi_fixed_freezing_escort_pairwise_tv_coalescence_exp_gapA_le_min
    (h : xi_fixed_freezing_escort_pairwise_tv_coalescence_data) :
    Real.exp (-h.gapA) ≤ Real.exp (-min h.gapA h.gapB) := by
  apply Real.exp_le_exp.mpr
  have hmin : min h.gapA h.gapB ≤ h.gapA := min_le_left _ _
  linarith

private lemma xi_fixed_freezing_escort_pairwise_tv_coalescence_exp_gapB_le_min
    (h : xi_fixed_freezing_escort_pairwise_tv_coalescence_data) :
    Real.exp (-h.gapB) ≤ Real.exp (-min h.gapA h.gapB) := by
  apply Real.exp_le_exp.mpr
  have hmin : min h.gapA h.gapB ≤ h.gapB := min_le_right _ _
  linarith

/-- Paper label: `cor:xi-fixed-freezing-escort-pairwise-tv-coalescence`. Passing both escort laws
through the same maximal-fiber reference measure yields a pairwise TV bound by the sum of the two
frozen envelopes, and the half-envelope normalization collapses that sum to the min-gap envelope.
-/
theorem paper_xi_fixed_freezing_escort_pairwise_tv_coalescence
    (h : xi_fixed_freezing_escort_pairwise_tv_coalescence_data) :
    h.tvDistance ≤ Real.exp (-h.gapA) + Real.exp (-h.gapB) ∧
      h.tvDistance ≤ Real.exp (-min h.gapA h.gapB) := by
  have hfirst : h.tvDistance ≤ Real.exp (-h.gapA) + Real.exp (-h.gapB) := by
    calc
      h.tvDistance ≤ h.referenceDistanceA + h.referenceDistanceB := h.triangle_bound
      _ ≤ (1 / 2 : ℝ) * Real.exp (-h.gapA) + (1 / 2 : ℝ) * Real.exp (-h.gapB) := by
            exact add_le_add h.referenceDistanceA_bound h.referenceDistanceB_bound
      _ ≤ Real.exp (-h.gapA) + Real.exp (-h.gapB) := by
            nlinarith [Real.exp_pos (-h.gapA), Real.exp_pos (-h.gapB)]
  have hgapA :
      (1 / 2 : ℝ) * Real.exp (-h.gapA) ≤ (1 / 2 : ℝ) * Real.exp (-min h.gapA h.gapB) := by
    exact mul_le_mul_of_nonneg_left
      (xi_fixed_freezing_escort_pairwise_tv_coalescence_exp_gapA_le_min h) (by norm_num)
  have hgapB :
      (1 / 2 : ℝ) * Real.exp (-h.gapB) ≤ (1 / 2 : ℝ) * Real.exp (-min h.gapA h.gapB) := by
    exact mul_le_mul_of_nonneg_left
      (xi_fixed_freezing_escort_pairwise_tv_coalescence_exp_gapB_le_min h) (by norm_num)
  have hsecond : h.tvDistance ≤ Real.exp (-min h.gapA h.gapB) := by
    calc
      h.tvDistance ≤ h.referenceDistanceA + h.referenceDistanceB := h.triangle_bound
      _ ≤ (1 / 2 : ℝ) * Real.exp (-h.gapA) + (1 / 2 : ℝ) * Real.exp (-h.gapB) := by
            exact add_le_add h.referenceDistanceA_bound h.referenceDistanceB_bound
      _ ≤ (1 / 2 : ℝ) * Real.exp (-min h.gapA h.gapB) +
            (1 / 2 : ℝ) * Real.exp (-min h.gapA h.gapB) := by
              exact add_le_add hgapA hgapB
      _ = Real.exp (-min h.gapA h.gapB) := by ring
  exact ⟨hfirst, hsecond⟩

end Omega.Zeta
