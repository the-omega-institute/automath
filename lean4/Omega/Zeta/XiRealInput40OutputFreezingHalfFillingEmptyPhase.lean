import Omega.Zeta.XiRealInput40OutputFreezingPositiveEntropyHalffill

namespace Omega.Zeta

/-- Paper label: `cor:xi-real-input-40-output-freezing-half-filling-empty-phase`. -/
theorem paper_xi_real_input_40_output_freezing_half_filling_empty_phase :
    xi_real_input_40_output_freezing_positive_entropy_halffill_left_endpoint_slope = 0 ∧
      xi_real_input_40_output_freezing_positive_entropy_halffill_right_endpoint_slope =
        (1 / 2 : ℝ) := by
  exact ⟨paper_xi_real_input_40_output_freezing_positive_entropy_halffill.1,
    paper_xi_real_input_40_output_freezing_positive_entropy_halffill.2.1⟩

end Omega.Zeta
