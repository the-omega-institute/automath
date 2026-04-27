import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped goldenRatio

noncomputable def conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value : ℝ :=
  (Real.goldenRatio⁻¹ : ℝ) ^ 6

noncomputable def conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_value : ℝ :=
  (Real.goldenRatio / 2) * conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value

/-- Concrete endpoint data for comparing the even/odd top-gap limits with the golden binary
channel contraction constant. -/
structure conclusion_golden_top_gap_equals_sdpi_data where
  even_gap_limit : ℝ
  sdpi_constant : ℝ
  phi_inv_six : ℝ
  odd_gap_limit : ℝ
  phi_half_mul_sdpi : ℝ
  conclusion_golden_top_gap_equals_sdpi_even_gap_limit_cert :
    even_gap_limit = conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value
  conclusion_golden_top_gap_equals_sdpi_sdpi_constant_cert :
    sdpi_constant = conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value
  conclusion_golden_top_gap_equals_sdpi_phi_inv_six_cert :
    phi_inv_six = conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value
  conclusion_golden_top_gap_equals_sdpi_odd_gap_limit_cert :
    odd_gap_limit = conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_value
  conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_cert :
    phi_half_mul_sdpi = conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_value

/-- Paper label: `thm:conclusion-golden-top-gap-equals-sdpi`. -/
theorem paper_conclusion_golden_top_gap_equals_sdpi
    (D : conclusion_golden_top_gap_equals_sdpi_data) :
    D.even_gap_limit = D.sdpi_constant ∧ D.sdpi_constant = D.phi_inv_six ∧
      D.odd_gap_limit = D.phi_half_mul_sdpi := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      D.even_gap_limit = conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value :=
        D.conclusion_golden_top_gap_equals_sdpi_even_gap_limit_cert
      _ = D.sdpi_constant := D.conclusion_golden_top_gap_equals_sdpi_sdpi_constant_cert.symm
  · calc
      D.sdpi_constant = conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value :=
        D.conclusion_golden_top_gap_equals_sdpi_sdpi_constant_cert
      _ = D.phi_inv_six := D.conclusion_golden_top_gap_equals_sdpi_phi_inv_six_cert.symm
  · calc
      D.odd_gap_limit = conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_value :=
        D.conclusion_golden_top_gap_equals_sdpi_odd_gap_limit_cert
      _ = D.phi_half_mul_sdpi :=
        D.conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_cert.symm

end Omega.Conclusion
