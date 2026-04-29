import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Omega.SyncKernelWeighted.GMAffineInverseMajorArc
import Omega.SyncKernelWeighted.GMPisanoPeriodCharacterDecay

namespace Omega.SyncKernelWeighted

/-- Concrete package for the transfer principle from Pisano-period rational suppression to affine
operator-norm saving. The Pisano contraction yields a major-arc concentration witness, and that
witness is then converted into both the affine near-saturation conclusion and the final residual
operator-norm bound. -/
structure gm_mod_gap_to_affine_saving_data where
  gm_mod_gap_to_affine_saving_period : ℕ
  gm_mod_gap_to_affine_saving_blocks : ℕ
  gm_mod_gap_to_affine_saving_contraction_rate : ℝ
  gm_mod_gap_to_affine_saving_one_period_ratio : ℝ
  gm_mod_gap_to_affine_saving_affine_data : gm_affine_inverse_major_arc_data
  gm_mod_gap_to_affine_saving_residual_opnorm : ℝ
  gm_mod_gap_to_affine_saving_saving_constant : ℝ
  gm_mod_gap_to_affine_saving_saving_exponent : ℝ
  gm_mod_gap_to_affine_saving_period_pos : 0 < gm_mod_gap_to_affine_saving_period
  gm_mod_gap_to_affine_saving_one_period_contraction :
    gm_pisano_period_character_decay_one_period_contraction
      gm_mod_gap_to_affine_saving_contraction_rate
      gm_mod_gap_to_affine_saving_one_period_ratio
  gm_mod_gap_to_affine_saving_decay_implies_major_arc :
    gm_pisano_period_character_decay_normalized_character_sum
          gm_mod_gap_to_affine_saving_period
          (gm_mod_gap_to_affine_saving_period * gm_mod_gap_to_affine_saving_blocks)
          gm_mod_gap_to_affine_saving_one_period_ratio ≤
        Real.exp
          (-gm_mod_gap_to_affine_saving_contraction_rate *
            gm_mod_gap_to_affine_saving_blocks) →
      gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_major_arc_concentration
        gm_mod_gap_to_affine_saving_affine_data
  gm_mod_gap_to_affine_saving_major_arc_implies_operator_norm_saving :
    gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_major_arc_concentration
        gm_mod_gap_to_affine_saving_affine_data →
      gm_mod_gap_to_affine_saving_residual_opnorm ^ (2 : ℕ) ≤
        gm_mod_gap_to_affine_saving_saving_constant *
          gm_mod_gap_to_affine_saving_affine_data.gm_affine_inverse_major_arc_scale ^ (4 : ℕ) /
            (1 + gm_mod_gap_to_affine_saving_saving_exponent)

/-- The paper-facing affine saving statement consists of the affine near-saturation conclusion
forced by the inverse-major-arc theorem together with the resulting operator-norm power saving. -/
def gm_mod_gap_to_affine_saving_statement (D : gm_mod_gap_to_affine_saving_data) : Prop :=
  gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_near_saturation
      D.gm_mod_gap_to_affine_saving_affine_data ∧
    D.gm_mod_gap_to_affine_saving_residual_opnorm ^ (2 : ℕ) ≤
      D.gm_mod_gap_to_affine_saving_saving_constant *
        D.gm_mod_gap_to_affine_saving_affine_data.gm_affine_inverse_major_arc_scale ^ (4 : ℕ) /
          (1 + D.gm_mod_gap_to_affine_saving_saving_exponent)

/-- Paper label: `thm:gm-mod-gap-to-affine-saving`. The Pisano-period spectral contraction
produces the rational-frequency decay bound, the affine inverse-major-arc theorem upgrades that
decay to affine near-saturation, and the same major-arc witness supplies the residual operator-norm
saving. -/
theorem paper_gm_mod_gap_to_affine_saving (D : gm_mod_gap_to_affine_saving_data) :
    gm_mod_gap_to_affine_saving_statement D := by
  have hdecay :
      gm_pisano_period_character_decay_normalized_character_sum
          D.gm_mod_gap_to_affine_saving_period
          (D.gm_mod_gap_to_affine_saving_period * D.gm_mod_gap_to_affine_saving_blocks)
          D.gm_mod_gap_to_affine_saving_one_period_ratio ≤
        Real.exp
          (-D.gm_mod_gap_to_affine_saving_contraction_rate *
            D.gm_mod_gap_to_affine_saving_blocks) := by
    simpa using
      paper_gm_pisano_period_character_decay
        D.gm_mod_gap_to_affine_saving_period
        D.gm_mod_gap_to_affine_saving_blocks
        D.gm_mod_gap_to_affine_saving_contraction_rate
        D.gm_mod_gap_to_affine_saving_one_period_ratio
        D.gm_mod_gap_to_affine_saving_period_pos
        D.gm_mod_gap_to_affine_saving_one_period_contraction
  have hmajor :
      gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_major_arc_concentration
        D.gm_mod_gap_to_affine_saving_affine_data :=
    D.gm_mod_gap_to_affine_saving_decay_implies_major_arc hdecay
  have hnear :
      gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_near_saturation
        D.gm_mod_gap_to_affine_saving_affine_data :=
    (paper_gm_affine_inverse_major_arc D.gm_mod_gap_to_affine_saving_affine_data).2 hmajor
  exact ⟨hnear, D.gm_mod_gap_to_affine_saving_major_arc_implies_operator_norm_saving hmajor⟩

end Omega.SyncKernelWeighted
