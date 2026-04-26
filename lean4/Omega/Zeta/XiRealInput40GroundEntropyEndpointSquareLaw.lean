import Mathlib.Tactic
import Omega.Zeta.XiRealInput40OutputFreezingPositiveEntropyHalffill

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-real-input-40-ground-entropy-endpoint-square-law`.
The positive-entropy half-fill theorem identifies the ground entropy with `log (sqrt 3)`, so
exponentiating gives the endpoint square law and the zero-temperature spectral scale. -/
theorem paper_xi_real_input_40_ground_entropy_endpoint_square_law :
    xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy =
        Real.log (Real.sqrt 3) ∧
      Real.exp (-2 * xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy) =
        (3 : ℝ)⁻¹ ∧
      Real.exp xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy =
        Real.sqrt 3 := by
  have hhalf := paper_xi_real_input_40_output_freezing_positive_entropy_halffill
  have hground :
      xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy =
        Real.log (Real.sqrt 3) := hhalf.2.2.2.1
  have hsqrt3_pos : 0 < (Real.sqrt 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ (2 : Nat) = 3 := by
    exact Real.sq_sqrt (by norm_num)
  have hexpGround :
      Real.exp xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy =
        Real.sqrt 3 := by
    rw [hground]
    exact Real.exp_log hsqrt3_pos
  have hexpTwo :
      Real.exp (2 * xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy) =
        (Real.sqrt 3 : ℝ) ^ (2 : Nat) := by
    calc
      Real.exp (2 * xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy)
          = Real.exp
              (xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy +
                xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy) := by
              ring_nf
      _ = Real.exp xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy *
          Real.exp xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy := by
            rw [Real.exp_add]
      _ = (Real.sqrt 3 : ℝ) * Real.sqrt 3 := by rw [hexpGround]
      _ = (Real.sqrt 3 : ℝ) ^ (2 : Nat) := by ring
  refine ⟨hground, ?_, hexpGround⟩
  calc
    Real.exp (-2 * xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy)
        = Real.exp (-(2 *
            xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy)) := by
            ring_nf
    _ =
        (Real.exp (2 *
          xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy))⁻¹ := by
          rw [Real.exp_neg]
    _ = ((Real.sqrt 3 : ℝ) ^ (2 : Nat))⁻¹ := by rw [hexpTwo]
    _ = (3 : ℝ)⁻¹ := by rw [hsqrt3_sq]

end

end Omega.Zeta
