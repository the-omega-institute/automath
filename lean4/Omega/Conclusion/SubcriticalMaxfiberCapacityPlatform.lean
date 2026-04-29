import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9tTopGapAffineCapacitySegment

namespace Omega.Conclusion

open Omega.Zeta

noncomputable section

/-- The exact `B`-budget capacity in the subcritical top-gap regime, obtained by substituting the
dyadic threshold `2^B` into the affine top-gap segment. -/
def conclusion_subcritical_maxfiber_capacity_platform_capacity
    (m K M B : ℕ) : ℤ :=
  xiTopGapCapacitySegment m K M (2 ^ B)

/-- The normalized success fraction attached to the subcritical max-fiber platform. -/
def conclusion_subcritical_maxfiber_capacity_platform_success
    (m K M B : ℕ) : ℝ :=
  (conclusion_subcritical_maxfiber_capacity_platform_capacity m K M B : ℝ) / (2 ^ m : ℝ)

/-- The corresponding normalized defect `1 - Succ_m(B)`. -/
def conclusion_subcritical_maxfiber_capacity_platform_defect
    (m K M B : ℕ) : ℝ :=
  1 - conclusion_subcritical_maxfiber_capacity_platform_success m K M B

/-- Paper-facing package for the subcritical max-fiber platform: once `2^B` lies strictly between
the second-largest and largest fiber sizes, the capacity is exactly affine, the defect factors as
the truncated top-gap mass divided by `2^m`, and the defect is strictly positive when at least one
maximal fiber is present. -/
def conclusion_subcritical_maxfiber_capacity_platform_statement : Prop :=
  ∀ m K M M₂ B : ℕ,
    0 < K →
    M₂ < 2 ^ B →
    2 ^ B < M →
      conclusion_subcritical_maxfiber_capacity_platform_capacity m K M B =
        (2 ^ m : ℤ) - (K : ℤ) * ((M - 2 ^ B : ℕ) : ℤ) ∧
      conclusion_subcritical_maxfiber_capacity_platform_defect m K M B =
        ((K : ℝ) * ((M - 2 ^ B : ℕ) : ℝ)) / (2 ^ m : ℝ) ∧
      0 < conclusion_subcritical_maxfiber_capacity_platform_defect m K M B

theorem paper_conclusion_subcritical_maxfiber_capacity_platform :
    conclusion_subcritical_maxfiber_capacity_platform_statement := by
  intro m K M M₂ B hK _hsecond hbudget
  have hseg := paper_xi_time_part9t_top_gap_affine_capacity_segment m K M (2 ^ B) hbudget
  have hcap :
      conclusion_subcritical_maxfiber_capacity_platform_capacity m K M B =
        (2 ^ m : ℤ) - (K : ℤ) * ((M - 2 ^ B : ℕ) : ℤ) := by
    simpa [conclusion_subcritical_maxfiber_capacity_platform_capacity] using hseg.1
  have hgap_nat : 0 < M - 2 ^ B := Nat.sub_pos_of_lt hbudget
  have hpow_pos : 0 < (2 ^ m : ℝ) := by positivity
  have hpow_ne : (2 ^ m : ℝ) ≠ 0 := ne_of_gt hpow_pos
  have hgap_pos : 0 < ((M - 2 ^ B : ℕ) : ℝ) := by
    exact_mod_cast hgap_nat
  have hK_pos : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hdefect :
      conclusion_subcritical_maxfiber_capacity_platform_defect m K M B =
        ((K : ℝ) * ((M - 2 ^ B : ℕ) : ℝ)) / (2 ^ m : ℝ) := by
    have hcap_real :
        (conclusion_subcritical_maxfiber_capacity_platform_capacity m K M B : ℝ) =
          (2 ^ m : ℝ) - (K : ℝ) * ((M - 2 ^ B : ℕ) : ℝ) := by
      exact_mod_cast hcap
    unfold conclusion_subcritical_maxfiber_capacity_platform_defect
      conclusion_subcritical_maxfiber_capacity_platform_success
    rw [hcap_real]
    field_simp [hpow_ne]
    ring
  refine ⟨hcap, hdefect, ?_⟩
  rw [hdefect]
  positivity

end

end Omega.Conclusion
