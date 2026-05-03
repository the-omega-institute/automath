import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-ed-xh-2torsion-dictionary-mod2`. -/
theorem paper_xi_ed_xh_2torsion_dictionary_mod2 (X : ℚ)
    (hX : (4 : ℚ) * X + 1 ≠ 0) :
    31 * (1 / (4 * X + 1)) ^ 3 - 13 * (1 / (4 * X + 1)) ^ 2 -
        3 * (1 / (4 * X + 1)) + 1 =
      16 * (4 * X ^ 3 - 4 * X + 1) / (4 * X + 1) ^ 3 := by
  field_simp [hX]
  ring

end Omega.Zeta
