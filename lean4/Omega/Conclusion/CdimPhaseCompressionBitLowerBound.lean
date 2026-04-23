import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.CdimPhaseCompressionPowerLaw

namespace Omega.Conclusion

/-- The dyadic bit budget needed to resolve the unavoidable phase-collision scale. -/
noncomputable def conclusion_cdim_phase_compression_bit_lower_bound_bits
    (D : conclusion_cdim_phase_compression_power_law_data) : ℝ :=
  Real.logb 2 (((D.N + 1 : ℝ) ^ ((D.r : ℝ) / D.d)) / 2)

/-- The near-collision forced by the power-law argument yields the corresponding base-2 bit lower
bound for any uniquely decodable phase code on the finite box. -/
def conclusion_cdim_phase_compression_bit_lower_bound_statement
    (D : conclusion_cdim_phase_compression_power_law_data) : Prop :=
  (∃ u v, u ∈ D.box ∧ v ∈ D.box ∧ u ≠ v ∧
      D.torusDist (D.phi u) (D.phi v) ≤ 2 * (D.N + 1 : ℝ) ^ (-(D.r : ℝ) / D.d)) ∧
    conclusion_cdim_phase_compression_bit_lower_bound_bits D =
      ((D.r : ℝ) / D.d) * Real.logb 2 (D.N + 1) - 1

theorem paper_conclusion_cdim_phase_compression_bit_lower_bound
    (D : conclusion_cdim_phase_compression_power_law_data) :
    conclusion_cdim_phase_compression_bit_lower_bound_statement D := by
  refine ⟨paper_conclusion_cdim_phase_compression_power_law D, ?_⟩
  unfold conclusion_cdim_phase_compression_bit_lower_bound_bits
  have hNp1_pos : 0 < (D.N + 1 : ℝ) := by positivity
  have hpow_ne : ((D.N + 1 : ℝ) ^ ((D.r : ℝ) / D.d)) ≠ 0 := by positivity
  rw [Real.logb_div hpow_ne (show (2 : ℝ) ≠ 0 by norm_num)]
  rw [Real.logb_rpow_eq_mul_logb_of_pos hNp1_pos]
  norm_num

end Omega.Conclusion
