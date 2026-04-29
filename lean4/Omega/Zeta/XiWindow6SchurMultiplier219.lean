import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-schur-multiplier-219`. -/
theorem paper_xi_window6_schur_multiplier_219
    (schurMultiplierRank cohomologyRank : Nat)
    (hschur :
      schurMultiplierRank =
        Nat.choose 8 2 + Nat.choose 4 2 + (9 + Nat.choose 9 2) + 8 * 4 + 8 * 9 + 4 * 9)
    (hcohom : cohomologyRank = schurMultiplierRank) :
    schurMultiplierRank = 219 ∧ cohomologyRank = 219 := by
  have hsum :
      Nat.choose 8 2 + Nat.choose 4 2 + (9 + Nat.choose 9 2) + 8 * 4 + 8 * 9 +
          4 * 9 =
        219 := by
    norm_num [Nat.choose]
  have hschur219 : schurMultiplierRank = 219 := by
    exact hschur.trans hsum
  exact ⟨hschur219, hcohom.trans hschur219⟩

end Omega.Zeta
