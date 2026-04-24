import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.CriticalCircleStateDimensionLB
import Omega.Zeta.XiCriticalLineHorizonCircle

namespace Omega.Zeta

/-- The `s`-plane real part attached to a spectral mode `μ` over a base `λ > 1`. -/
noncomputable def rhSPlaneRe (lambda : ℝ) (mu : ℂ) : ℝ :=
  Real.log ‖mu‖ / Real.log lambda

private lemma sqrt_lambda_gt_one {lambda : ℝ} (hlambda : 1 < lambda) :
    1 < Real.sqrt lambda := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt zero_le_one hlambda

private lemma rhSPlaneRe_gt_half_iff {lambda : ℝ} (hlambda : 1 < lambda) (mu : ℂ) :
    Real.sqrt lambda < ‖mu‖ ↔ 1 / 2 < rhSPlaneRe lambda mu := by
  have hloglambda : 0 < Real.log lambda := Real.log_pos hlambda
  have hlambda_nonneg : 0 ≤ lambda := le_trans zero_le_one hlambda.le
  have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.2 (lt_trans zero_lt_one hlambda)
  constructor
  · intro hmu
    have hlog : Real.log (Real.sqrt lambda) < Real.log ‖mu‖ :=
      (Real.log_lt_log_iff hsqrt_pos (lt_trans hsqrt_pos hmu)).2 hmu
    have hlog' : Real.log lambda / 2 < Real.log ‖mu‖ := by
      simpa [Real.log_sqrt hlambda_nonneg] using hlog
    rw [rhSPlaneRe, lt_div_iff₀ hloglambda]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog'
  · intro hs
    rw [rhSPlaneRe] at hs
    have hlog' : Real.log lambda / 2 < Real.log ‖mu‖ := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (lt_div_iff₀ hloglambda).1 hs
    have hlog : Real.log (Real.sqrt lambda) < Real.log ‖mu‖ := by
      simpa [Real.log_sqrt hlambda_nonneg] using hlog'
    have hmu_pos : 0 < ‖mu‖ := by
      by_contra hnonpos
      have hzero : ‖mu‖ = 0 := le_antisymm (le_of_not_gt hnonpos) (norm_nonneg _)
      rw [hzero, Real.log_zero] at hlog
      exact (not_lt_of_ge (show Real.log (Real.sqrt lambda) ≥ 0 by
        have hsqrt_gt_one := sqrt_lambda_gt_one hlambda
        exact (Real.log_nonneg hsqrt_gt_one.le)) hlog).elim
    exact (Real.log_lt_log_iff hsqrt_pos hmu_pos).1 hlog

private lemma rhSPlaneRe_eq_half_iff {lambda : ℝ} (hlambda : 1 < lambda) (mu : ℂ) :
    ‖mu‖ = Real.sqrt lambda ↔ rhSPlaneRe lambda mu = 1 / 2 := by
  have hloglambda : 0 < Real.log lambda := Real.log_pos hlambda
  have hlambda_nonneg : 0 ≤ lambda := le_trans zero_le_one hlambda.le
  have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.2 (lt_trans zero_lt_one hlambda)
  constructor
  · intro hmu
    rw [rhSPlaneRe, hmu, Real.log_sqrt hlambda_nonneg]
    field_simp [hloglambda.ne']
  · intro hs
    rw [rhSPlaneRe] at hs
    have hlog : Real.log ‖mu‖ = Real.log (Real.sqrt lambda) := by
      have hs' : 2 * Real.log ‖mu‖ = Real.log lambda := by
        field_simp [hloglambda.ne'] at hs
        linarith
      have hlog' : Real.log ‖mu‖ = Real.log lambda / 2 := by
        linarith
      simpa [Real.log_sqrt hlambda_nonneg] using hlog'
    have hmu_pos : 0 < ‖mu‖ := by
      by_contra hnonpos
      have hzero : ‖mu‖ = 0 := le_antisymm (le_of_not_gt hnonpos) (norm_nonneg _)
      rw [hzero, Real.log_zero] at hlog
      have hsqrt_gt_one := sqrt_lambda_gt_one hlambda
      have hsqrt_log_pos : 0 < Real.log (Real.sqrt lambda) := Real.log_pos hsqrt_gt_one
      linarith
    exact Real.strictMonoOn_log.injOn (by simpa using hmu_pos) (by simpa using hsqrt_pos) hlog

/-- The RH stratification for spectral modes translates exactly into the `s`-plane trichotomy via
`Re(s) = log |μ| / log λ`: outside/inside the critical circle becomes right/left of `Re(s)=1/2`,
and the critical circle itself becomes the critical line.
    cor:rh-stratification-splane -/
theorem paper_rh_stratification_splane {lambda : ℝ} (hlambda : 1 < lambda) (mu : ℂ) :
    (Real.sqrt lambda < ‖mu‖ ↔ 1 / 2 < rhSPlaneRe lambda mu) ∧
    (‖mu‖ = Real.sqrt lambda ↔ rhSPlaneRe lambda mu = 1 / 2) ∧
    (‖mu‖ < Real.sqrt lambda ↔ rhSPlaneRe lambda mu < 1 / 2) := by
  have hgt := rhSPlaneRe_gt_half_iff hlambda mu
  have heq := rhSPlaneRe_eq_half_iff hlambda mu
  refine ⟨hgt, heq, ?_⟩
  constructor
  · intro hlt
    by_contra hnotlt
    have hge : 1 / 2 ≤ rhSPlaneRe lambda mu := le_of_not_gt hnotlt
    rcases lt_or_eq_of_le hge with hgt' | heq'
    · exact (not_lt_of_ge (hgt.mpr hgt').le) hlt
    · exact (ne_of_lt hlt) (heq.mpr heq'.symm)
  · intro hlt
    by_contra hnotlt
    have hge : Real.sqrt lambda ≤ ‖mu‖ := le_of_not_gt hnotlt
    rcases lt_or_eq_of_le hge with hmu_gt | hmu_eq
    · have : 1 / 2 < rhSPlaneRe lambda mu := hgt.mp hmu_gt
      exact (not_lt_of_ge this.le) hlt
    · exact (ne_of_lt hlt) (heq.mp hmu_eq.symm)

end Omega.Zeta
