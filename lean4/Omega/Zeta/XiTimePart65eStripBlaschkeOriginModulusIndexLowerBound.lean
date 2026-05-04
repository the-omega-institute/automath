import Omega.Zeta.XiTimePart65eBlaschkeOriginModulusDimensionBound

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label:
`thm:xi-time-part65e-strip-blaschke-origin-modulus-index-lower-bound`. -/
theorem paper_xi_time_part65e_strip_blaschke_origin_modulus_index_lower_bound
    (D : xi_offslice_realpart_sum_law_data) (eta : ℝ) (heta : 0 < eta)
    (hupper : ∀ j : Fin D.n, D.rePart j - (1 / 2 : ℝ) ≤ eta) :
    xi_offslice_realpart_sum_law_weight D / (2 * D.L * eta) ≤ (D.n : ℝ) ∧
      -Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L * eta) ≤
        (D.n : ℝ) := by
  rcases paper_xi_offslice_realpart_sum_law D with ⟨_, _, htotal⟩
  have hdeviation_upper :
      xi_offslice_realpart_sum_law_total_deviation D ≤ (D.n : ℝ) * eta := by
    unfold xi_offslice_realpart_sum_law_total_deviation
    calc
      ∑ j : Fin D.n, (D.rePart j - (1 / 2 : ℝ)) ≤ ∑ _j : Fin D.n, eta := by
        exact Finset.sum_le_sum fun j _hj => hupper j
      _ = (D.n : ℝ) * eta := by simp
  have hweight_div :
      xi_offslice_realpart_sum_law_weight D / (2 * D.L) / eta ≤ (D.n : ℝ) := by
    rw [← htotal.1]
    exact (div_le_iff₀ heta).2 hdeviation_upper
  have horigin_div :
      (-Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L)) / eta ≤
        (D.n : ℝ) := by
    rw [← htotal.2]
    exact (div_le_iff₀ heta).2 hdeviation_upper
  constructor
  · calc
      xi_offslice_realpart_sum_law_weight D / (2 * D.L * eta) =
          xi_offslice_realpart_sum_law_weight D / (2 * D.L) / eta := by
        rw [div_div]
      _ ≤ (D.n : ℝ) := hweight_div
  · calc
      -Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L * eta) =
          (-Real.log (xi_offslice_realpart_sum_law_origin_modulus D) / (2 * D.L)) /
            eta := by
        rw [div_div]
      _ ≤ (D.n : ℝ) := horigin_div

end

end Omega.Zeta
