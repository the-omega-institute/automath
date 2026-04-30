import Mathlib.Analysis.SpecificLimits.Basic
import Omega.Conclusion.MaxfiberAverageScaleRigidity

open Filter
open scoped Topology goldenRatio

namespace Omega.Conclusion

noncomputable section

private lemma conclusion_maxfiber_noncondensation_law_constant_pos :
    0 < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
  positivity

private lemma conclusion_maxfiber_noncondensation_law_constant_gt_one :
    1 < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
  have hphi_sq_gt_sqrt5 : Real.sqrt 5 < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    exact Omega.Entropy.phi_add_one_gt_sqrt5
  exact (one_lt_div (by positivity : 0 < Real.sqrt 5)).2 hphi_sq_gt_sqrt5

/-- Paper label: `thm:conclusion-maxfiber-noncondensation-law`. -/
theorem paper_conclusion_maxfiber_noncondensation_law :
    Tendsto
        (fun m : ℕ =>
          (1 : ℝ) / (m : ℝ) *
            Real.log
              (conclusion_maxfiber_average_scale_rigidity_M m /
                conclusion_maxfiber_average_scale_rigidity_avg m))
        atTop (nhds 0) ∧
      Tendsto
        (fun m : ℕ =>
          conclusion_maxfiber_average_scale_rigidity_M m /
            conclusion_maxfiber_average_scale_rigidity_avg m)
        atTop (nhds (Real.goldenRatio ^ 2 / Real.sqrt 5)) ∧
      0 < Real.goldenRatio ^ 2 / Real.sqrt 5 - 1 := by
  have hratio := paper_conclusion_maxfiber_average_scale_rigidity
  have hlog :
      Tendsto
        (fun m : ℕ =>
          Real.log
            (conclusion_maxfiber_average_scale_rigidity_M m /
              conclusion_maxfiber_average_scale_rigidity_avg m))
        atTop (nhds (Real.log (Real.goldenRatio ^ 2 / Real.sqrt 5))) := by
    exact
      (Real.continuousAt_log
        (ne_of_gt conclusion_maxfiber_noncondensation_law_constant_pos)).tendsto.comp hratio
  have hone :
      Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfirst :
      Tendsto
        (fun m : ℕ =>
          (1 : ℝ) / (m : ℝ) *
            Real.log
              (conclusion_maxfiber_average_scale_rigidity_M m /
                conclusion_maxfiber_average_scale_rigidity_avg m))
        atTop (nhds 0) := by
    simpa using hone.mul hlog
  exact
    ⟨hfirst, hratio,
      sub_pos.mpr conclusion_maxfiber_noncondensation_law_constant_gt_one⟩

end

end Omega.Conclusion
