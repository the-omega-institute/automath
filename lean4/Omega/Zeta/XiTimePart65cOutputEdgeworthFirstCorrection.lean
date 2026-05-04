import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- Concrete data for the first Edgeworth correction of the centered output count. -/
structure xi_time_part65c_output_edgeworth_first_correction_data where
  xi_time_part65c_output_edgeworth_first_correction_outputCDF : ℕ → ℝ → ℝ
  xi_time_part65c_output_edgeworth_first_correction_normalCDF : ℝ → ℝ
  xi_time_part65c_output_edgeworth_first_correction_normalPDF : ℝ → ℝ
  xi_time_part65c_output_edgeworth_first_correction_sigma : ℝ
  xi_time_part65c_output_edgeworth_first_correction_kappa3 : ℝ
  xi_time_part65c_output_edgeworth_first_correction_standardizedSkewness : ℝ
  xi_time_part65c_output_edgeworth_first_correction_remainderScale : ℕ → ℝ
  xi_time_part65c_output_edgeworth_first_correction_sigma_pos :
    0 < xi_time_part65c_output_edgeworth_first_correction_sigma
  xi_time_part65c_output_edgeworth_first_correction_kappa3_neg :
    xi_time_part65c_output_edgeworth_first_correction_kappa3 < 0
  xi_time_part65c_output_edgeworth_first_correction_standardizedSkewness_eq :
    xi_time_part65c_output_edgeworth_first_correction_standardizedSkewness =
      xi_time_part65c_output_edgeworth_first_correction_kappa3 /
        xi_time_part65c_output_edgeworth_first_correction_sigma ^ (3 : ℕ)
  xi_time_part65c_output_edgeworth_first_correction_edgeworthExpansion_h :
    ∀ x : ℝ,
      (fun n : ℕ =>
          xi_time_part65c_output_edgeworth_first_correction_outputCDF n x -
            (xi_time_part65c_output_edgeworth_first_correction_normalCDF x +
              xi_time_part65c_output_edgeworth_first_correction_kappa3 /
                  (6 * xi_time_part65c_output_edgeworth_first_correction_sigma ^ (3 : ℕ)) *
                (1 - x ^ (2 : ℕ)) *
                xi_time_part65c_output_edgeworth_first_correction_normalPDF x /
                Real.sqrt n)) =O[atTop]
          xi_time_part65c_output_edgeworth_first_correction_remainderScale

namespace xi_time_part65c_output_edgeworth_first_correction_data

/-- The imported quasipowers Edgeworth expansion, specialized to the first correction. -/
def edgeworthExpansion (D : xi_time_part65c_output_edgeworth_first_correction_data) : Prop :=
  ∀ x : ℝ,
    (fun n : ℕ =>
        D.xi_time_part65c_output_edgeworth_first_correction_outputCDF n x -
          (D.xi_time_part65c_output_edgeworth_first_correction_normalCDF x +
            D.xi_time_part65c_output_edgeworth_first_correction_kappa3 /
                (6 * D.xi_time_part65c_output_edgeworth_first_correction_sigma ^ (3 : ℕ)) *
              (1 - x ^ (2 : ℕ)) *
              D.xi_time_part65c_output_edgeworth_first_correction_normalPDF x /
              Real.sqrt n)) =O[atTop]
        D.xi_time_part65c_output_edgeworth_first_correction_remainderScale

/-- The standardized skewness constant `kappa_3 / sigma^3`. -/
def standardizedSkewness
    (D : xi_time_part65c_output_edgeworth_first_correction_data) : ℝ :=
  D.xi_time_part65c_output_edgeworth_first_correction_standardizedSkewness

end xi_time_part65c_output_edgeworth_first_correction_data

/-- Paper label: `thm:xi-time-part65c-output-edgeworth-first-correction`. -/
theorem paper_xi_time_part65c_output_edgeworth_first_correction
    (D : xi_time_part65c_output_edgeworth_first_correction_data) :
    D.edgeworthExpansion ∧ D.standardizedSkewness < 0 := by
  constructor
  · exact D.xi_time_part65c_output_edgeworth_first_correction_edgeworthExpansion_h
  · have hsigma3_pos :
        0 < D.xi_time_part65c_output_edgeworth_first_correction_sigma ^ (3 : ℕ) := by
      exact pow_pos D.xi_time_part65c_output_edgeworth_first_correction_sigma_pos _
    rw [xi_time_part65c_output_edgeworth_first_correction_data.standardizedSkewness,
      D.xi_time_part65c_output_edgeworth_first_correction_standardizedSkewness_eq]
    exact div_neg_of_neg_of_pos
      D.xi_time_part65c_output_edgeworth_first_correction_kappa3_neg hsigma3_pos

end

end Omega.Zeta
