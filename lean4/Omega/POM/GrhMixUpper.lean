import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-grh-mix-upper`. A square-root spectral bound gives a logarithmic
gap lower bound, hence the reciprocal mixing-time upper bound. -/
theorem paper_pom_grh_mix_upper (lambda1 Lambda g tauMix : ℝ) (hlambda : 1 < lambda1)
    (hLambda_pos : 0 < Lambda) (hgrh : Lambda ≤ Real.sqrt lambda1)
    (hg : g = Real.log (lambda1 / Lambda)) (htau : tauMix = 1 / g) :
    (1 / 2 * Real.log lambda1 ≤ g) ∧ (tauMix ≤ 2 / Real.log lambda1) := by
  have hlambda_pos : 0 < lambda1 := by linarith
  have hsqrt_pos : 0 < Real.sqrt lambda1 := Real.sqrt_pos_of_pos hlambda_pos
  have hratio_lower : Real.sqrt lambda1 ≤ lambda1 / Lambda := by
    rw [le_div_iff₀ hLambda_pos]
    calc
      Real.sqrt lambda1 * Lambda ≤ Real.sqrt lambda1 * Real.sqrt lambda1 :=
        mul_le_mul_of_nonneg_left hgrh (le_of_lt hsqrt_pos)
      _ = lambda1 := by
        rw [← sq, Real.sq_sqrt (le_of_lt hlambda_pos)]
  have hlog_lower : 1 / 2 * Real.log lambda1 ≤ g := by
    rw [hg]
    have hlog := Real.log_le_log hsqrt_pos hratio_lower
    rw [Real.log_sqrt (le_of_lt hlambda_pos)] at hlog
    linarith
  have hhalf_pos : 0 < 1 / 2 * Real.log lambda1 := by
    have hlog_pos : 0 < Real.log lambda1 := Real.log_pos hlambda
    positivity
  have htau_bound : tauMix ≤ 2 / Real.log lambda1 := by
    rw [htau]
    have hrecip := one_div_le_one_div_of_le hhalf_pos hlog_lower
    convert hrecip using 1
    field_simp [ne_of_gt (Real.log_pos hlambda)]
  exact ⟨hlog_lower, htau_bound⟩

end Omega.POM
