import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.AffineRegisterBudget

namespace Omega.Conclusion

open scoped Real

/-- The logarithmic two-circle threshold from the rate/circle-dimension budget inequality. -/
noncomputable def rateCdimThreshold : ℝ :=
  Real.log 2 / Real.log Real.goldenRatio

/-- The one-circle residual gap. -/
noncomputable def oneCircleGap : ℝ :=
  Real.log (2 / Real.goldenRatio) / Real.log Real.goldenRatio

lemma oneCircleGap_eq_threshold_sub_one :
    oneCircleGap = rateCdimThreshold - 1 := by
  unfold oneCircleGap rateCdimThreshold
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_ne : Real.goldenRatio ≠ 0 := ne_of_gt hphi_pos
  have hlog_ne : Real.log Real.goldenRatio ≠ 0 := by
    exact ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  rw [Real.log_div (by positivity) hphi_ne]
  field_simp [hlog_ne]

lemma rateCdimThreshold_gt_one : 1 < rateCdimThreshold := by
  unfold rateCdimThreshold
  have hlogphi_pos : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hlog_lt : Real.log Real.goldenRatio < Real.log 2 := by
    exact Real.log_lt_log Real.goldenRatio_pos Real.goldenRatio_lt_two
  have hdiv :
      Real.log Real.goldenRatio / Real.log Real.goldenRatio <
        Real.log 2 / Real.log Real.goldenRatio := by
    rw [div_lt_div_iff_of_pos_right hlogphi_pos]
    simpa
  have hlog_ne : Real.log Real.goldenRatio ≠ 0 := ne_of_gt hlogphi_pos
  have hone : Real.log Real.goldenRatio / Real.log Real.goldenRatio = 1 := by
    field_simp [hlog_ne]
  rw [hone] at hdiv
  simpa using hdiv

lemma oneCircleGap_pos : 0 < oneCircleGap := by
  rw [oneCircleGap_eq_threshold_sub_one]
  linarith [rateCdimThreshold_gt_one]

/-- Paper label statement for the two-circle threshold and one-circle gap corollary. -/
def paper_conclusion_rate_cdim_two_circle_threshold : Prop :=
  (∀ k : ℕ, rateCdimThreshold ≤ k → 2 ≤ k) ∧
    (∀ r : ℝ, rateCdimThreshold ≤ 1 + r → oneCircleGap ≤ r) ∧
    oneCircleGap = rateCdimThreshold - 1 ∧
    0 < oneCircleGap

/-- Proof witness for the paper-facing two-circle threshold package. -/
theorem paper_conclusion_rate_cdim_two_circle_threshold_proof :
    paper_conclusion_rate_cdim_two_circle_threshold := by
  refine ⟨?_, ?_, oneCircleGap_eq_threshold_sub_one, oneCircleGap_pos⟩
  · intro k hk
    have hk_real : (1 : ℝ) < k := lt_of_lt_of_le rateCdimThreshold_gt_one hk
    have hk_nat : 1 < k := by
      exact_mod_cast hk_real
    omega
  · intro r hr
    rw [oneCircleGap_eq_threshold_sub_one]
    linarith

end Omega.Conclusion
