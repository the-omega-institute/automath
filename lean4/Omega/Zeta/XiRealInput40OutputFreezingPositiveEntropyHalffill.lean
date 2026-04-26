import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40AlphaMax
import Omega.SyncKernelWeighted.RealInput40GroundEntropy
import Omega.SyncKernelWeighted.RealInput40PositiveEntropyFreezing

namespace Omega.Zeta

open Omega.SyncKernelWeighted

noncomputable section

/-- Explicit `4 × 4` zero-temperature matrix for the positive-bias real-input-`40` freezing
chapter. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_zero_temp_matrix :
    Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 1, 1, 0;
    0, 0, 1, 0;
    0, 0, 3, 1;
    1, 0, 0, 3]

/-- Left endpoint slope of the freezing profile. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_left_endpoint_slope : ℝ :=
  0

/-- Right endpoint slope of the positive-bias freezing profile. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_right_endpoint_slope : ℝ :=
  real_input_40_alpha_max_value

/-- Ground entropy of the positive-bias zero-temperature four-state model. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy : ℝ :=
  realInput40GroundEntropy (Real.sqrt 3)

/-- The positive-bias zero-temperature density window stays inside `[0, 1/2]`. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_density_window (α : ℝ) : Prop :=
  0 ≤ α ∧ α ≤
    xi_real_input_40_output_freezing_positive_entropy_halffill_right_endpoint_slope

/-- A finite periodic-orbit collapse would force the chapter-local ground entropy to vanish. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_finite_periodic_orbit_collapse :
    Prop :=
  xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy = 0

/-- Paper label: `thm:xi-real-input-40-output-freezing-positive-entropy-halffill`. The endpoint
slopes are `0` and `1/2`, the positive-bias zero-temperature witness is the explicit four-state
matrix `B_∞`, the associated ground entropy is `log (√3) > 0`, and therefore the positive-bias
freezing endpoint cannot collapse to finitely many periodic orbits. -/
def xi_real_input_40_output_freezing_positive_entropy_halffill_statement : Prop :=
  xi_real_input_40_output_freezing_positive_entropy_halffill_left_endpoint_slope = 0 ∧
    xi_real_input_40_output_freezing_positive_entropy_halffill_right_endpoint_slope = (1 / 2 : ℝ) ∧
    xi_real_input_40_output_freezing_positive_entropy_halffill_zero_temp_matrix =
      !![0, 1, 1, 0;
        0, 0, 1, 0;
        0, 0, 3, 1;
        1, 0, 0, 3] ∧
    xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy =
      Real.log (Real.sqrt 3) ∧
    0 < xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy ∧
    xi_real_input_40_output_freezing_positive_entropy_halffill_density_window
      xi_real_input_40_output_freezing_positive_entropy_halffill_right_endpoint_slope ∧
    ¬ xi_real_input_40_output_freezing_positive_entropy_halffill_finite_periodic_orbit_collapse

theorem paper_xi_real_input_40_output_freezing_positive_entropy_halffill :
    xi_real_input_40_output_freezing_positive_entropy_halffill_statement := by
  have hsqrt3_nonneg : 0 ≤ (Real.sqrt 3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  have hsqrt3_gt_one : 1 < (Real.sqrt 3 : ℝ) := by
    nlinarith
  have hfreeze := paper_killo_real_input_40_positive_entropy_freezing (Real.sqrt 3) hsqrt3_gt_one
  have halpha := paper_real_input_40_alpha_max
  refine ⟨rfl, halpha.2.2.2.2, rfl, hfreeze.2.1, hfreeze.1, ?_, ?_⟩
  · refine ⟨?_, le_rfl⟩
    rw [xi_real_input_40_output_freezing_positive_entropy_halffill_right_endpoint_slope,
      halpha.2.2.2.2]
    norm_num
  · intro hcollapse
    have hzero : realInput40GroundEntropy (Real.sqrt 3) = 0 := by
      simpa [xi_real_input_40_output_freezing_positive_entropy_halffill_finite_periodic_orbit_collapse,
        xi_real_input_40_output_freezing_positive_entropy_halffill_ground_entropy] using hcollapse
    exact (ne_of_gt hfreeze.1) hzero

end

end Omega.Zeta
