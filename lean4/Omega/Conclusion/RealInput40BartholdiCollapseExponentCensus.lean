import Mathlib.Tactic
import Omega.Zeta.RealInput40BartholdiEscapeInitialForms

namespace Omega.Conclusion

open Omega.Zeta

/-- The factor `(1 + t (1 - t) z^2)^2` contributes four additional square-root branches. -/
def conclusion_realinput40_bartholdi_collapse_exponent_census_extra_half_branches : ℕ := 4

/-- Paper label: `thm:conclusion-realinput40-bartholdi-collapse-exponent-census`.
The Newton--Puiseux spectrum contributes `2/8/3` branches of exponents `1, 1/2, 1/3`, and the
extra squared quadratic factor contributes four more `1/2`-branches, yielding the exact
`2/12/3` collapse census. -/
theorem paper_conclusion_real_input_40_bartholdi_collapse_exponent_census :
    realInput40BartholdiEscapeSlope 0 = 1 ∧
      realInput40BartholdiEscapeMultiplicity 0 = 2 ∧
      realInput40BartholdiEscapeSlope 1 = 1 / 2 ∧
      realInput40BartholdiEscapeMultiplicity 1 +
          conclusion_realinput40_bartholdi_collapse_exponent_census_extra_half_branches = 12 ∧
      realInput40BartholdiEscapeSlope 2 = 1 / 3 ∧
      realInput40BartholdiEscapeMultiplicity 2 = 3 ∧
      realInput40BartholdiEscapeMultiplicity 0 +
          (realInput40BartholdiEscapeMultiplicity 1 +
            conclusion_realinput40_bartholdi_collapse_exponent_census_extra_half_branches) +
          realInput40BartholdiEscapeMultiplicity 2 = 17 := by
  rcases paper_real_input_40_bartholdi_escape_initial_forms with
    ⟨_, hs0, _, hm0, hs1, _, _, hm1, hs2, _, hm2, _⟩
  refine ⟨hs0, hm0, hs1, ?_, hs2, hm2, ?_⟩
  · rw [hm1]
    norm_num [conclusion_realinput40_bartholdi_collapse_exponent_census_extra_half_branches]
  · rw [hm0, hm1, hm2]
    norm_num [conclusion_realinput40_bartholdi_collapse_exponent_census_extra_half_branches]

end Omega.Conclusion
