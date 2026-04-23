import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- The centered log-multiplicity observable `Y_m = (log d - log M) / m`. -/
noncomputable def xi_time_part9u_frozen_escort_logmultiplicity_mgf_centered_logmultiplicity
    (logd logM m : ℝ) : ℝ :=
  (logd - logM) / m

/-- The normalized frozen-phase mgf ratio `S_(a+t)/(M^t S_a)` written abstractly. -/
noncomputable def xi_time_part9u_frozen_escort_logmultiplicity_mgf_ratio
    (Sa Sat scale : ℝ) : ℝ :=
  Sat / (scale * Sa)

/-- The spectral-gap exponent entering the frozen mgf ratio estimate. -/
def xi_time_part9u_frozen_escort_logmultiplicity_mgf_delta
    (deltaA deltaAt : ℝ) : ℝ :=
  min deltaA deltaAt

/-- Paper label: `thm:xi-time-part9u-frozen-escort-logmultiplicity-mgf`. In the frozen phase,
every centered log-multiplicity `(log d - log M) / m` is nonpositive, a pair of exponentially
small relative remainders gives an exponentially rigid normalized mgf ratio, and the same
off-ground exponential mass bound propagates directly to every `L^r` envelope with fixed radius
`C`. -/
theorem paper_xi_time_part9u_frozen_escort_logmultiplicity_mgf
    (m logM baseA scale epsilonA epsilonAt deltaA deltaAt C massOff : ℝ) (r : ℕ)
    (hm : 0 < m) (hbaseA : 0 < baseA) (hscale : 0 < scale) (hdeltaA : 0 ≤ deltaA)
    (hdeltaAt : 0 ≤ deltaAt) (hepsilonA : |epsilonA| ≤ Real.exp (-deltaA) / 2)
    (hepsilonAt : |epsilonAt| ≤ Real.exp (-deltaAt) / 2)
    (hmassOff : massOff ≤ Real.exp (-deltaA)) (hC : 0 ≤ C) :
    (∀ logd : ℝ,
      logd ≤ logM →
        xi_time_part9u_frozen_escort_logmultiplicity_mgf_centered_logmultiplicity
            logd logM m ≤ 0) ∧
      (let Sa := baseA * (1 + epsilonA)
       let Sat := scale * baseA * (1 + epsilonAt)
       let delta :=
         xi_time_part9u_frozen_escort_logmultiplicity_mgf_delta deltaA deltaAt
       xi_time_part9u_frozen_escort_logmultiplicity_mgf_ratio Sa Sat scale =
           (1 + epsilonAt) / (1 + epsilonA) ∧
         |xi_time_part9u_frozen_escort_logmultiplicity_mgf_ratio Sa Sat scale - 1| ≤
           2 * Real.exp (-delta) ∧
         C ^ r * massOff ≤ C ^ r * Real.exp (-deltaA)) := by
  refine ⟨?_, ?_⟩
  · intro logd hlogd
    unfold xi_time_part9u_frozen_escort_logmultiplicity_mgf_centered_logmultiplicity
    rw [div_eq_mul_inv]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlogd) (inv_nonneg.mpr hm.le)
  · dsimp [xi_time_part9u_frozen_escort_logmultiplicity_mgf_delta,
      xi_time_part9u_frozen_escort_logmultiplicity_mgf_ratio]
    have hExpA_le_one : Real.exp (-deltaA) ≤ 1 := by
      have hneg : -deltaA ≤ 0 := by linarith
      simpa using Real.exp_le_one_iff.mpr hneg
    have hExpAt_le_one : Real.exp (-deltaAt) ≤ 1 := by
      have hneg : -deltaAt ≤ 0 := by linarith
      simpa using Real.exp_le_one_iff.mpr hneg
    have hAbsA_half : |epsilonA| ≤ (1 : ℝ) / 2 := by
      have hhalf : Real.exp (-deltaA) / 2 ≤ (1 : ℝ) / 2 := by
        exact (div_le_div_of_nonneg_right hExpA_le_one (by norm_num : (0 : ℝ) ≤ 2))
      exact le_trans hepsilonA hhalf
    have hAbsAt_half : |epsilonAt| ≤ (1 : ℝ) / 2 := by
      have hhalf : Real.exp (-deltaAt) / 2 ≤ (1 : ℝ) / 2 := by
        exact (div_le_div_of_nonneg_right hExpAt_le_one (by norm_num : (0 : ℝ) ≤ 2))
      exact le_trans hepsilonAt hhalf
    have hden_lower : (1 : ℝ) / 2 ≤ 1 + epsilonA := by
      have hneg : -(1 : ℝ) / 2 ≤ epsilonA := by
        linarith [neg_abs_le epsilonA, hAbsA_half]
      linarith
    have hden_pos : 0 < 1 + epsilonA := by
      linarith
    have hratio :
        (scale * baseA * (1 + epsilonAt)) /
            (scale * (baseA * (1 + epsilonA))) =
          (1 + epsilonAt) / (1 + epsilonA) := by
      field_simp [hscale.ne', hbaseA.ne']
    refine ⟨hratio, ?_, ?_⟩
    · have hmain :
          |(1 + epsilonAt) / (1 + epsilonA) - 1| ≤ 2 * |epsilonAt - epsilonA| := by
        have habs :
            |(1 + epsilonAt) / (1 + epsilonA) - 1| =
              |epsilonAt - epsilonA| / |1 + epsilonA| := by
          have hrew : (1 + epsilonAt) / (1 + epsilonA) - 1 = (epsilonAt - epsilonA) / (1 + epsilonA) := by
            field_simp [hden_pos.ne']
            ring
          rw [hrew, abs_div]
        rw [habs]
        have hhalf_inv : |1 + epsilonA|⁻¹ ≤ 2 := by
          have habs_eq : |1 + epsilonA| = 1 + epsilonA := abs_of_pos hden_pos
          rw [habs_eq]
          have hrecip : 1 / (1 + epsilonA) ≤ 1 / ((1 : ℝ) / 2) := by
            exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hden_lower
          simpa [one_div] using hrecip
        have hnonneg : 0 ≤ |epsilonAt - epsilonA| := abs_nonneg _
        calc
          |epsilonAt - epsilonA| / |1 + epsilonA|
              = |epsilonAt - epsilonA| * |1 + epsilonA|⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ |epsilonAt - epsilonA| * 2 := by
                exact mul_le_mul_of_nonneg_left hhalf_inv hnonneg
          _ = 2 * |epsilonAt - epsilonA| := by ring
      have hdeltaA :
          Real.exp (-deltaA) ≤ Real.exp (-min deltaA deltaAt) := by
        apply Real.exp_le_exp.mpr
        have hmin : min deltaA deltaAt ≤ deltaA := min_le_left _ _
        linarith
      have hdeltaAt :
          Real.exp (-deltaAt) ≤ Real.exp (-min deltaA deltaAt) := by
        apply Real.exp_le_exp.mpr
        have hmin : min deltaA deltaAt ≤ deltaAt := min_le_right _ _
        linarith
      have hsum :
          |epsilonAt| + |epsilonA| ≤ Real.exp (-min deltaA deltaAt) := by
        have h1 : |epsilonAt| ≤ Real.exp (-min deltaA deltaAt) / 2 := by
          have hdiv :
              Real.exp (-deltaAt) / 2 ≤ Real.exp (-min deltaA deltaAt) / 2 := by
            exact div_le_div_of_nonneg_right hdeltaAt (by norm_num : (0 : ℝ) ≤ 2)
          exact le_trans hepsilonAt hdiv
        have h2 : |epsilonA| ≤ Real.exp (-min deltaA deltaAt) / 2 := by
          have hdiv :
              Real.exp (-deltaA) / 2 ≤ Real.exp (-min deltaA deltaAt) / 2 := by
            exact div_le_div_of_nonneg_right hdeltaA (by norm_num : (0 : ℝ) ≤ 2)
          exact le_trans hepsilonA hdiv
        linarith
      have hsub : |epsilonAt - epsilonA| ≤ |epsilonAt| + |epsilonA| := by
        rw [abs_sub_le_iff]
        constructor <;> nlinarith [neg_abs_le epsilonAt, le_abs_self epsilonAt,
          neg_abs_le epsilonA, le_abs_self epsilonA]
      have hgoal :
          |(scale * baseA * (1 + epsilonAt)) /
                (scale * (baseA * (1 + epsilonA))) - 1| ≤
            2 * Real.exp (-min deltaA deltaAt) := by
        calc
        |(scale * baseA * (1 + epsilonAt)) /
              (scale * (baseA * (1 + epsilonA))) - 1|
            = |(1 + epsilonAt) / (1 + epsilonA) - 1| := by rw [hratio]
        _ ≤ 2 * |epsilonAt - epsilonA| := hmain
        _ ≤ 2 * (|epsilonAt| + |epsilonA|) := by
              gcongr
        _ ≤ 2 * Real.exp (-min deltaA deltaAt) := by
              gcongr
      exact hgoal
    · have hpow_nonneg : 0 ≤ C ^ r := pow_nonneg hC r
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hmassOff hpow_nonneg

end Omega.Zeta
