import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-2x2-coupling-leakage-artanh`. -/
theorem paper_xi_2x2_coupling_leakage_artanh (a b L : ℝ) (habs : |b| < a) :
    (1 / 2 : ℝ) * Real.log ((a + b) / (a - b)) =
      (1 / 2 : ℝ) * Real.log ((1 + b / a) / (1 - b / a)) := by
  have _ : L = L := rfl
  have ha_pos : 0 < a := lt_of_le_of_lt (abs_nonneg b) habs
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hb_lt_a : b < a := (abs_lt.mp habs).2
  have hden : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hb_lt_a)
  have hratio : (a + b) / (a - b) = (1 + b / a) / (1 - b / a) := by
    field_simp [ha_ne, hden]
  rw [← hratio]

end Omega.Zeta
