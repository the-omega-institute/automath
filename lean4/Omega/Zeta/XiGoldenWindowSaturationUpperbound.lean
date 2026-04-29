import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Omega.Zeta.XiSingleDefectIntegratedClosedForm

namespace Omega.Zeta

open Real

lemma xi_golden_window_saturation_upperbound_arctan_le_self {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x := by
  have hatan_nonneg : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr hx
  have hatan_lt : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  simpa using (Real.le_tan hatan_nonneg hatan_lt)

lemma xi_golden_window_saturation_upperbound_arctan_div_sub_le {X a b : ℝ}
    (hX : 0 < X) (hab : b ≤ a) :
    Real.arctan (a / X) - Real.arctan (b / X) ≤ (a - b) / X := by
  have hdiv_le : b / X ≤ a / X := by
    exact div_le_div_of_nonneg_right hab hX.le
  have hnonneg : 0 ≤ (a - b) / X := by
    exact div_nonneg (sub_nonneg.mpr hab) hX.le
  have hdiff_nonneg :
      0 ≤ Real.arctan (a / X) - Real.arctan (b / X) := by
    exact sub_nonneg.mpr (Real.arctan_mono hdiv_le)
  have harg_nonneg : 0 ≤ a / X - b / X := sub_nonneg.mpr hdiv_le
  have hlip :
      ‖Real.arctan (a / X) - Real.arctan (b / X)‖ ≤ 1 * ‖a / X - b / X‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := Real.arctan) (C := (1 : ℝ))
      (fun x _ => Real.differentiableAt_arctan x) ?_ convex_univ (Set.mem_univ _) (Set.mem_univ _)
    intro x _
    have hden_ge : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hden_pos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hrecip : 1 / (1 + x ^ 2) ≤ (1 : ℝ) := by
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden_ge)
    have hrecip_nonneg : 0 ≤ 1 / (1 + x ^ 2) := div_nonneg zero_le_one hden_pos.le
    simpa [Real.deriv_arctan, Real.norm_eq_abs, abs_of_nonneg hrecip_nonneg,
      abs_of_pos hden_pos, one_div] using hrecip
  have harg_eq : a / X - b / X = (a - b) / X := by ring
  have hnorm_diff :
      ‖Real.arctan (a / X) - Real.arctan (b / X)‖ =
        Real.arctan (a / X) - Real.arctan (b / X) := by
    simp [Real.norm_eq_abs, abs_of_nonneg hdiff_nonneg]
  have hnorm_arg : ‖a / X - b / X‖ = (a - b) / X := by
    rw [harg_eq]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sub_nonneg.mpr hab), abs_of_pos hX]
  simpa [hnorm_diff, hnorm_arg] using hlip

/-- Paper label: `cor:xi-golden-window-saturation-upperbound`. The closed arctangent form
saturates to `2πδ`, and the finite-window deficit is bounded by `8δ / X`. -/
theorem paper_xi_golden_window_saturation_upperbound
    (D : XiSingleDefectIntegratedClosedFormData)
    (hX : 0 < singleDefectSupportRadius D.ρ D.δ) :
    0 ≤ 2 * Real.pi * D.δ - D.defectIntegral ∧
      2 * Real.pi * D.δ - D.defectIntegral ≤
        8 * D.δ / singleDefectSupportRadius D.ρ D.δ := by
  let X := singleDefectSupportRadius D.ρ D.δ
  let A : ℝ := 1 + D.δ
  let B : ℝ := 1 - D.δ
  have hXpos : 0 < X := by simpa [X] using hX
  have hApos : 0 < A := by
    dsimp [A]
    linarith [D.hδ.1]
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [D.hδ.2]
  have hBA : B ≤ A := by
    dsimp [A, B]
    linarith [D.hδ.1]
  have hAdiv_nonneg : 0 ≤ A / X := div_nonneg hApos.le hXpos.le
  have hBdiv_nonneg : 0 ≤ B / X := div_nonneg hBpos.le hXpos.le
  have hAcomp :
      Real.arctan (X / A) = Real.pi / 2 - Real.arctan (A / X) := by
    have hdiv_pos : 0 < A / X := div_pos hApos hXpos
    have hrewrite : X / A = (A / X)⁻¹ := by
      field_simp [hApos.ne', hXpos.ne']
    rw [hrewrite, Real.arctan_inv_of_pos hdiv_pos]
  have hBcomp :
      Real.arctan (X / B) = Real.pi / 2 - Real.arctan (B / X) := by
    have hdiv_pos : 0 < B / X := div_pos hBpos hXpos
    have hrewrite : X / B = (B / X)⁻¹ := by
      field_simp [hBpos.ne', hXpos.ne']
    rw [hrewrite, Real.arctan_inv_of_pos hdiv_pos]
  have hclosed := (paper_xi_single_defect_integrated_closed_form D).2
  have hgap_eq :
      2 * Real.pi * D.δ - D.defectIntegral =
        2 * A * Real.arctan (A / X) - 2 * B * Real.arctan (B / X) := by
    calc
      2 * Real.pi * D.δ - D.defectIntegral
          = 2 * Real.pi * D.δ -
              (2 * A * Real.arctan (X / A) - 2 * B * Real.arctan (X / B)) := by
                simpa [X, A, B] using congrArg (fun t => 2 * Real.pi * D.δ - t) hclosed
      _ = 2 * A * Real.arctan (A / X) - 2 * B * Real.arctan (B / X) := by
            rw [hAcomp, hBcomp]
            ring
  have hgap_nonneg :
      0 ≤ 2 * A * Real.arctan (A / X) - 2 * B * Real.arctan (B / X) := by
    have hterm_nonneg : 0 ≤ (A - B) * Real.arctan (A / X) := by
      exact mul_nonneg (sub_nonneg.mpr hBA) (Real.arctan_nonneg.mpr hAdiv_nonneg)
    have hdiff_nonneg : 0 ≤ B * (Real.arctan (A / X) - Real.arctan (B / X)) := by
      exact mul_nonneg hBpos.le (sub_nonneg.mpr (Real.arctan_mono
        (div_le_div_of_nonneg_right hBA hXpos.le)))
    nlinarith
  have hdiff_le :
      Real.arctan (A / X) - Real.arctan (B / X) ≤ (A - B) / X :=
    xi_golden_window_saturation_upperbound_arctan_div_sub_le hXpos hBA
  have hAatan_le : Real.arctan (A / X) ≤ A / X :=
    xi_golden_window_saturation_upperbound_arctan_le_self hAdiv_nonneg
  have hgap_le :
      2 * A * Real.arctan (A / X) - 2 * B * Real.arctan (B / X) ≤ 8 * D.δ / X := by
    have hdecomp :
        2 * A * Real.arctan (A / X) - 2 * B * Real.arctan (B / X) =
          2 * ((A - B) * Real.arctan (A / X) +
            B * (Real.arctan (A / X) - Real.arctan (B / X))) := by ring
    rw [hdecomp]
    have hfirst :
        (A - B) * Real.arctan (A / X) ≤ (A - B) * (A / X) := by
      exact mul_le_mul_of_nonneg_left hAatan_le (sub_nonneg.mpr hBA)
    have hsecond :
        B * (Real.arctan (A / X) - Real.arctan (B / X)) ≤ B * ((A - B) / X) := by
      exact mul_le_mul_of_nonneg_left hdiff_le hBpos.le
    have hsum :
        (A - B) * Real.arctan (A / X) +
            B * (Real.arctan (A / X) - Real.arctan (B / X)) ≤
          (A - B) * (A / X) + B * ((A - B) / X) := add_le_add hfirst hsecond
    have hbound :
        2 * ((A - B) * Real.arctan (A / X) +
            B * (Real.arctan (A / X) - Real.arctan (B / X))) ≤
          2 * ((A - B) * (A / X) + B * ((A - B) / X)) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hright :
        2 * ((A - B) * (A / X) + B * ((A - B) / X)) = 8 * D.δ / X := by
      field_simp [hXpos.ne']
      ring
    simpa [hright] using hbound
  exact ⟨by simpa [hgap_eq] using hgap_nonneg, by simpa [X, hgap_eq] using hgap_le⟩

end Omega.Zeta
