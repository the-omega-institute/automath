import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete singular-radius data for
`thm:conclusion-finite-cyclotomic-surgery-positive-exponent-transparency`.  The core
singular radius is positive; the finite cyclotomic surgery adds only unit-radius singularities,
so the post-surgery singular radius is the minimum of the core radius and `1`. -/
structure conclusion_finite_cyclotomic_surgery_positive_exponent_transparency_Data where
  lambda : ℝ
  coreRadius : ℝ
  rhoCore : ℝ
  rhoN : ℝ
  thetaCore : ℝ
  thetaN : ℝ
  lambda_gt_one : 1 < lambda
  coreRadius_pos : 0 < coreRadius
  rhoCore_eq : rhoCore = coreRadius⁻¹
  rhoN_eq : rhoN = (min 1 coreRadius)⁻¹
  thetaCore_eq : thetaCore = Real.log rhoCore / Real.log lambda
  thetaN_eq : thetaN = Real.log rhoN / Real.log lambda

lemma conclusion_finite_cyclotomic_surgery_positive_exponent_transparency_inv_min
    (r : ℝ) (hr : 0 < r) : (min 1 r)⁻¹ = max 1 r⁻¹ := by
  by_cases h : r ≤ 1
  · have hinv_ge : 1 ≤ r⁻¹ := (one_le_inv₀ hr).2 h
    simp [min_eq_right h, max_eq_right hinv_ge]
  · have h_one_le : 1 ≤ r := le_of_lt (lt_of_not_ge h)
    have hinv_le : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h_one_le
    simp [min_eq_left h_one_le, max_eq_left hinv_le]

lemma conclusion_finite_cyclotomic_surgery_positive_exponent_transparency_log_max
    (lambda r : ℝ) (hlambda : 1 < lambda) (hr : 0 < r) :
    Real.log (max 1 r) / Real.log lambda = max 0 (Real.log r / Real.log lambda) := by
  have hlog_lambda_pos : 0 < Real.log lambda := Real.log_pos hlambda
  by_cases h : r ≤ 1
  · have hlog_nonpos : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hr) h
    have hdiv_nonpos : Real.log r / Real.log lambda ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog_nonpos hlog_lambda_pos.le
    simp [max_eq_left h, max_eq_left hdiv_nonpos]
  · have h_one_le : 1 ≤ r := le_of_lt (lt_of_not_ge h)
    have hlog_nonneg : 0 ≤ Real.log r := Real.log_nonneg h_one_le
    have hdiv_nonneg : 0 ≤ Real.log r / Real.log lambda :=
      div_nonneg hlog_nonneg hlog_lambda_pos.le
    simp [max_eq_right h_one_le, max_eq_right hdiv_nonneg]

/-- Paper label:
`thm:conclusion-finite-cyclotomic-surgery-positive-exponent-transparency`. -/
theorem paper_conclusion_finite_cyclotomic_surgery_positive_exponent_transparency
    (D : conclusion_finite_cyclotomic_surgery_positive_exponent_transparency_Data) :
    D.rhoN = max 1 D.rhoCore ∧ D.thetaN = max 0 D.thetaCore ∧
      ∀ tau : ℝ, 0 < tau → (D.thetaN > tau ↔ D.thetaCore > tau) := by
  have hrhoCore_pos : 0 < D.rhoCore := by
    rw [D.rhoCore_eq]
    exact inv_pos.mpr D.coreRadius_pos
  have hrho : D.rhoN = max 1 D.rhoCore := by
    calc
      D.rhoN = (min 1 D.coreRadius)⁻¹ := D.rhoN_eq
      _ = max 1 D.coreRadius⁻¹ :=
        conclusion_finite_cyclotomic_surgery_positive_exponent_transparency_inv_min
          D.coreRadius D.coreRadius_pos
      _ = max 1 D.rhoCore := by rw [← D.rhoCore_eq]
  have htheta : D.thetaN = max 0 D.thetaCore := by
    calc
      D.thetaN = Real.log D.rhoN / Real.log D.lambda := D.thetaN_eq
      _ = Real.log (max 1 D.rhoCore) / Real.log D.lambda := by rw [hrho]
      _ = max 0 (Real.log D.rhoCore / Real.log D.lambda) :=
        conclusion_finite_cyclotomic_surgery_positive_exponent_transparency_log_max
          D.lambda D.rhoCore D.lambda_gt_one hrhoCore_pos
      _ = max 0 D.thetaCore := by rw [← D.thetaCore_eq]
  refine ⟨hrho, htheta, ?_⟩
  intro tau htau
  constructor
  · intro hN
    rw [htheta] at hN
    by_contra hcore
    have hcore_le : D.thetaCore ≤ tau := le_of_not_gt hcore
    have hmax_le : max 0 D.thetaCore ≤ tau := max_le (le_of_lt htau) hcore_le
    linarith
  · intro hcore
    rw [htheta]
    exact lt_of_lt_of_le hcore (le_max_right 0 D.thetaCore)

end

end Omega.Conclusion
