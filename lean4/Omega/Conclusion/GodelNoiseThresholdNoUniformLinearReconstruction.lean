import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.GodelAlgorithmicSufficiencyMetricInstabilitySeparation
import Omega.SPG.NoiseBudget

namespace Omega.Conclusion

/-- Concrete data for the linear reconstruction obstruction above the `2^{-m/2}` noise scale. -/
structure conclusion_godel_noise_threshold_no_uniform_linear_reconstruction_data where
  algData : Omega.SPG.StokesGodelAlgorithmicHolographicCompletenessData
  n : ℕ
  m : ℕ
  δ : ℝ
  ε : ℝ
  hn : 0 < n
  hδ : 0 ≤ δ
  hε : 0 ≤ ε
  hNoise :
    Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) < ε

/-- The algorithmic sufficiency package survives, but the linear noise budget fails once the
noise exceeds the sharp `2^{-m/2}` threshold. -/
def conclusion_godel_noise_threshold_no_uniform_linear_reconstruction_data.obstruction
    (D : conclusion_godel_noise_threshold_no_uniform_linear_reconstruction_data) : Prop :=
  (D.algData.complexityPreserved ∧ D.algData.bulkRecoverableFromCode ∧
      D.algData.volumeComputableFromCode) ∧
    ¬ (((1 / Real.sqrt (2 * D.n : ℝ)) * (2 : ℝ) ^ (D.m / 2 : ℝ)) * D.ε ≤ D.δ)

/-- Paper label: `cor:conclusion-godel-noise-threshold-no-uniform-linear-reconstruction`. -/
theorem paper_conclusion_godel_noise_threshold_no_uniform_linear_reconstruction
    (D : conclusion_godel_noise_threshold_no_uniform_linear_reconstruction_data) :
    D.obstruction := by
  have hsep :=
    paper_conclusion_godel_algorithmic_sufficiency_metric_instability_separation D.algData
  refine ⟨hsep.1, ?_⟩
  intro hlinear
  have hbudget :=
    Omega.SPG.paper_noiseBudget_threshold_iff (n := D.n) (m := D.m) (ε := D.ε) (δ := D.δ) D.hn
  have hthreshold :
      D.ε ≤ Real.sqrt (2 * D.n : ℝ) * D.δ * (2 : ℝ) ^ (-(D.m / 2 : ℝ)) := by
    exact hbudget.mp hlinear
  exact not_le_of_gt D.hNoise hthreshold

end Omega.Conclusion
