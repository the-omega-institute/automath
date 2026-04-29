import Omega.Zeta.XiOffsliceBlaschkeOriginModulus

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label: `thm:xi-time-part65e-blaschke-origin-modulus-dimension-bound`. -/
theorem paper_xi_time_part65e_blaschke_origin_modulus_dimension_bound
    (D : xi_offslice_realpart_sum_law_data) (deltaMin : ℝ) (hdelta_pos : 0 < deltaMin)
    (hdelta : ∀ j : Fin D.n, deltaMin ≤ D.rePart j - (1 / 2 : ℝ)) :
    (D.n : ℝ) ≤ xi_offslice_realpart_sum_law_weight D / (2 * D.L * deltaMin) ∧
      (D.n : ℝ) ≤
        -Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L * deltaMin) := by
  rcases paper_xi_offslice_realpart_sum_law D with ⟨_, _, htotal⟩
  have hdeviation_lower :
      (D.n : ℝ) * deltaMin ≤ xi_offslice_realpart_sum_law_total_deviation D := by
    unfold xi_offslice_realpart_sum_law_total_deviation
    calc
      (D.n : ℝ) * deltaMin = ∑ _j : Fin D.n, deltaMin := by simp
      _ ≤ ∑ j : Fin D.n, (D.rePart j - (1 / 2 : ℝ)) := by
          exact Finset.sum_le_sum fun j _hj => hdelta j
  have hweight_div :
      (D.n : ℝ) ≤ xi_offslice_realpart_sum_law_weight D / (2 * D.L) / deltaMin := by
    rw [← htotal.1]
    exact (le_div_iff₀ hdelta_pos).2 hdeviation_lower
  have horigin_div :
      (D.n : ℝ) ≤
        (-Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L)) /
          deltaMin := by
    rw [← htotal.2]
    exact (le_div_iff₀ hdelta_pos).2 hdeviation_lower
  constructor
  · calc
      (D.n : ℝ) ≤ xi_offslice_realpart_sum_law_weight D / (2 * D.L) / deltaMin :=
        hweight_div
      _ = xi_offslice_realpart_sum_law_weight D / (2 * D.L * deltaMin) := by
        rw [div_div]
  · calc
      (D.n : ℝ) ≤
          (-Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L)) /
            deltaMin := horigin_div
      _ =
          -Real.log (xi_offslice_realpart_sum_law_origin_modulus D) /
            (2 * D.L * deltaMin) := by
        rw [div_div]

end

end Omega.Zeta
