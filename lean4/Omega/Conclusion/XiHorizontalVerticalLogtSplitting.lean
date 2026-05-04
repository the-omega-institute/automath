import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-xi-horizontal-vertical-logt-splitting`.

The vertical drift bound divided by a separated horizontal scale gives the stated
`log t`-level split. -/
theorem paper_conclusion_xi_horizontal_vertical_logt_splitting
    (sigma gamma tau E t c C1 C2 : ℝ) (hc : 0 < c) (hE : 0 < E) (ht : 1 < t)
    (hsep : c * E ≤ |gamma - tau|)
    (hvert : |sigma - 1 / 2| ≤ C1 * E / Real.log t + C2 / (t * Real.log t)) :
    ∃ C1' C2' : ℝ,
      |sigma - 1 / 2| / |gamma - tau| ≤
        C1' / Real.log t + C2' / (t * Real.log t) * E⁻¹ := by
  refine ⟨C1 / c, C2 / c, ?_⟩
  have hlog : 0 < Real.log t := Real.log_pos ht
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hscale_pos : 0 < c * E := mul_pos hc hE
  have hden_pos : 0 < |gamma - tau| := hscale_pos.trans_le hsep
  have hnonneg : 0 ≤ C1 * E / Real.log t + C2 / (t * Real.log t) :=
    (abs_nonneg _).trans hvert
  have hdiv₁ :
      |sigma - 1 / 2| / |gamma - tau| ≤
        (C1 * E / Real.log t + C2 / (t * Real.log t)) / |gamma - tau| :=
    div_le_div_of_nonneg_right hvert hden_pos.le
  have hdiv₂ :
      (C1 * E / Real.log t + C2 / (t * Real.log t)) / |gamma - tau| ≤
        (C1 * E / Real.log t + C2 / (t * Real.log t)) / (c * E) := by
    exact div_le_div_of_nonneg_left hnonneg hscale_pos hsep
  calc
    |sigma - 1 / 2| / |gamma - tau| ≤
        (C1 * E / Real.log t + C2 / (t * Real.log t)) / |gamma - tau| := hdiv₁
    _ ≤ (C1 * E / Real.log t + C2 / (t * Real.log t)) / (c * E) := hdiv₂
    _ = (C1 / c) / Real.log t + (C2 / c) / (t * Real.log t) * E⁻¹ := by
      field_simp [hc.ne', hE.ne', hlog.ne', htpos.ne']

end Omega.Conclusion
