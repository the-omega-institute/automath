import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.XiCdimPhaseCompressionAliasingExponent

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-cdim-precision-conservation-law`. Once the separation scale is the power
law `B^(-(r / d))`, any admissible precision `ε` must satisfy the corresponding logarithmic lower
bound. -/
theorem paper_xi_cdim_precision_conservation_law (r d : ℕ) (hd : 0 < d) {B ε : ℝ}
    (hB : 1 < B) (hε : 0 < ε)
    (hsep : ε ≤ Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta r d B) :
    (d : ℝ) * Real.log (1 / ε) ≥ (r : ℝ) * Real.log B := by
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hdelta_pos :
      0 < Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta r d B := by
    unfold Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta
    positivity
  have hrecip :
      1 / Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta r d B ≤ 1 / ε := by
    exact one_div_le_one_div_of_le hε hsep
  have hlog :
      Real.log (1 / Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta r d B) ≤
        Real.log (1 / ε) := by
    exact Real.log_le_log (one_div_pos.mpr hdelta_pos) hrecip
  have hphase := paper_xi_cdim_phase_compression_aliasing_exponent r d hd hB
  dsimp at hphase
  have hdelta_log :
      Real.log (1 / Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta r d B) =
        ((r : ℝ) / d) * Real.log B := by
    rw [hphase.2.1, Real.log_rpow hB0]
  have hmain : ((r : ℝ) / d) * Real.log B ≤ Real.log (1 / ε) := by
    calc
      ((r : ℝ) / d) * Real.log B =
          Real.log (1 / Omega.Zeta.xi_cdim_phase_compression_aliasing_exponent_delta r d B) := by
            rw [hdelta_log]
      _ ≤ Real.log (1 / ε) := hlog
  have hmuld :
      (d : ℝ) * (((r : ℝ) / d) * Real.log B) ≤ (d : ℝ) * Real.log (1 / ε) := by
    exact mul_le_mul_of_nonneg_left hmain (le_of_lt hd_pos)
  calc
    (d : ℝ) * Real.log (1 / ε) ≥ (d : ℝ) * (((r : ℝ) / d) * Real.log B) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmuld
    _ = ((d : ℝ) * ((r : ℝ) / d)) * Real.log B := by ring
    _ = (r : ℝ) * Real.log B := by
      field_simp [hd_pos.ne']

end

end Omega.Zeta
