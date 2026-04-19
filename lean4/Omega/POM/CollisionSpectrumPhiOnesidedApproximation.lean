import Mathlib
import Omega.POM.RqQinftyEndpoint

namespace Omega.POM

/-- The raw one-sided collision-spectrum estimator written in the `φ * exp(2 * error)` form. -/
noncomputable def pomCollisionSpectrumPhiRawEstimator (L x : ℝ) : ℝ :=
  Real.goldenRatio * Real.exp (2 * (L - x))

set_option maxHeartbeats 400000 in
/-- The endpoint bound on `h_q / q` turns the raw estimator into a one-sided approximation to `φ`:
rewriting the estimator as `φ * exp(2 * (L - h_q / q))` makes the upper/lower bounds, the
logarithmic error, and the additive error all immediate from monotonicity of `exp` and `log`.
`thm:pom-collision-spectrum-phi-onesided-approximation` -/
theorem paper_pom_collision_spectrum_phi_onesided_approximation
    (rqRoot hq Dq : ℕ → ℝ)
    (hbound : ∀ q, 2 ≤ q →
      Real.sqrt Real.goldenRatio ≤ rqRoot q ∧
        rqRoot q ≤
          Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ)))
    (hhq : ∀ q, 2 ≤ q → hq q / (q : ℝ) = Real.log (2 / rqRoot q))
    (hDq : ∀ q, 2 ≤ q →
      Dq q = (hq q / ((q : ℝ) - 1)) * (Real.log Real.goldenRatio)⁻¹)
    (q : ℕ) (hq_ge : 2 ≤ q) :
    let L := Real.log (2 / Real.sqrt Real.goldenRatio)
    let estimator := pomCollisionSpectrumPhiRawEstimator L (hq q / (q : ℝ))
    Real.goldenRatio ≤ estimator ∧
      estimator ≤ Real.goldenRatio * Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) ∧
      Real.log estimator = Real.log Real.goldenRatio + 2 * (L - hq q / (q : ℝ)) ∧
      0 ≤ Real.log estimator - Real.log Real.goldenRatio ∧
      Real.log estimator - Real.log Real.goldenRatio ≤
        2 * Real.log Real.goldenRatio / (q : ℝ) ∧
      0 ≤ estimator - Real.goldenRatio ∧
      estimator - Real.goldenRatio ≤
        Real.goldenRatio * (Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) - 1) := by
  set L : ℝ := Real.log (2 / Real.sqrt Real.goldenRatio)
  set err : ℝ := L - hq q / (q : ℝ)
  set estimator : ℝ := pomCollisionSpectrumPhiRawEstimator L (hq q / (q : ℝ))
  change
    Real.goldenRatio ≤ estimator ∧
      estimator ≤ Real.goldenRatio * Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) ∧
      Real.log estimator = Real.log Real.goldenRatio + 2 * (L - hq q / (q : ℝ)) ∧
      0 ≤ Real.log estimator - Real.log Real.goldenRatio ∧
      Real.log estimator - Real.log Real.goldenRatio ≤
        2 * Real.log Real.goldenRatio / (q : ℝ) ∧
      0 ≤ estimator - Real.goldenRatio ∧
      estimator - Real.goldenRatio ≤
        Real.goldenRatio * (Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) - 1)
  have hendpoint := paper_pom_rq_qinfty_endpoint rqRoot hq Dq hbound hhq hDq
  have herr : 0 ≤ err ∧ err ≤ Real.log Real.goldenRatio / (q : ℝ) := by
    simpa [L, err] using hendpoint.2.2.2.2 q hq_ge
  have herr_nonneg : 0 ≤ err := herr.1
  have herr_upper : err ≤ Real.log Real.goldenRatio / (q : ℝ) := herr.2
  have hexp_lower : 1 ≤ Real.exp (2 * err) := by
    have hcmp : Real.exp 0 ≤ Real.exp (2 * err) := by
      exact Real.exp_le_exp.mpr (by nlinarith [herr_nonneg])
    simpa using hcmp
  have hexp_upper :
      Real.exp (2 * err) ≤ Real.exp (2 * (Real.log Real.goldenRatio / (q : ℝ))) := by
    exact Real.exp_le_exp.mpr (by nlinarith [herr_upper])
  have hexp_upper' :
      Real.exp (2 * err) ≤ Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) := by
    simpa [mul_div_assoc] using hexp_upper
  have hlog_estimator :
      Real.log estimator = Real.log Real.goldenRatio + 2 * err := by
    dsimp [estimator, pomCollisionSpectrumPhiRawEstimator]
    rw [Real.log_mul (by positivity) (by exact ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hestimator_lower : Real.goldenRatio ≤ estimator := by
    dsimp [estimator, pomCollisionSpectrumPhiRawEstimator]
    have hmul := mul_le_mul_of_nonneg_left hexp_lower Real.goldenRatio_pos.le
    simpa using hmul
  have hestimator_upper :
      estimator ≤ Real.goldenRatio * Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) := by
    dsimp [estimator, pomCollisionSpectrumPhiRawEstimator]
    exact mul_le_mul_of_nonneg_left hexp_upper' Real.goldenRatio_pos.le
  have hlog_error :
      Real.log estimator - Real.log Real.goldenRatio = 2 * err := by
    linarith [hlog_estimator]
  have hlog_error_nonneg : 0 ≤ Real.log estimator - Real.log Real.goldenRatio := by
    rw [hlog_error]
    nlinarith [herr_nonneg]
  have hlog_error_upper :
      Real.log estimator - Real.log Real.goldenRatio ≤
        2 * Real.log Real.goldenRatio / (q : ℝ) := by
    rw [hlog_error]
    have : 2 * err ≤ 2 * (Real.log Real.goldenRatio / (q : ℝ)) := by
      nlinarith [herr_upper]
    simpa [mul_div_assoc] using this
  have hadditive :
      estimator - Real.goldenRatio = Real.goldenRatio * (Real.exp (2 * err) - 1) := by
    dsimp [estimator, pomCollisionSpectrumPhiRawEstimator]
    ring
  have hadditive_nonneg : 0 ≤ estimator - Real.goldenRatio := by
    rw [hadditive]
    have : 0 ≤ Real.exp (2 * err) - 1 := by
      linarith [hexp_lower]
    exact mul_nonneg Real.goldenRatio_pos.le this
  have hadditive_upper :
      estimator - Real.goldenRatio ≤
        Real.goldenRatio * (Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) - 1) := by
    rw [hadditive]
    have hsub :
        Real.exp (2 * err) - 1 ≤ Real.exp (2 * Real.log Real.goldenRatio / (q : ℝ)) - 1 := by
      exact sub_le_sub_right hexp_upper' 1
    exact mul_le_mul_of_nonneg_left hsub Real.goldenRatio_pos.le
  exact ⟨hestimator_lower, hestimator_upper, by simpa [err] using hlog_estimator,
    hlog_error_nonneg, hlog_error_upper, hadditive_nonneg, hadditive_upper⟩

end Omega.POM
