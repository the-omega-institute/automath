import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:abel-offcritical-exponential-radius-amplification`. The lower bound on the
scale `m` is equivalent to a logarithmic upper bound on the off-critical radius, and exponentiating
that inequality gives the desired `rpow` estimate. -/
theorem paper_abel_offcritical_exponential_radius_amplification {b ε δ η : ℝ} {m : ℕ}
    (hb : 1 < b) (_hε : 0 < ε) (_hδ : 0 ≤ δ) (hδε : δ < ε) (hη0 : 0 < η) (_hη1 : η < 1)
    (hm : Real.log (1 / η) / ((ε - δ) * Real.log b) ≤ (m : ℝ)) :
    Real.rpow b (-((m : ℝ) * (ε - δ))) ≤ η := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hεδ : 0 < ε - δ := sub_pos.mpr hδε
  have hden : 0 < (ε - δ) * Real.log b := mul_pos hεδ hlogb
  have hmul :
      Real.log (1 / η) ≤ (m : ℝ) * ((ε - δ) * Real.log b) := by
    exact (div_le_iff₀ hden).mp hm
  have hloginv : Real.log (1 / η) = -Real.log η := by
    rw [one_div, Real.log_inv]
  have hneg :
      (-((m : ℝ) * (ε - δ))) * Real.log b ≤ Real.log η := by
    nlinarith [hmul, hloginv]
  calc
    Real.rpow b (-((m : ℝ) * (ε - δ))) = Real.exp (Real.log b * (-((m : ℝ) * (ε - δ)))) := by
      simpa using (Real.rpow_def_of_pos hb0 (-((m : ℝ) * (ε - δ))))
    _ ≤ Real.exp (Real.log η) := by
      exact Real.exp_le_exp.2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hneg)
    _ = η := by rw [Real.exp_log hη0]

end Omega.Zeta
