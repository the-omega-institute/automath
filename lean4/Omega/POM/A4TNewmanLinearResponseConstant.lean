import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The requested paper signature for `prop:pom-a4t-newman-linear-response-constant` is false as
stated: at `zStar = 2`, the displayed rational formula defines `cStar`, but the claimed octic in
`cStar` does not vanish. This concrete witness justifies leaving the paper statement marked as
partial until the missing Newman-root hypothesis is added to the Lean signature. -/
theorem pom_a4t_newman_linear_response_constant_counterexample :
    let zStar : ℝ := 2
    let cStar : ℝ := 4088 / 40205
    1 < zStar ∧
      cStar =
        (zStar ^ 3 * (3 * zStar ^ 8 + 3 * zStar ^ 7 - 6 * zStar ^ 4 - 7 * zStar ^ 3 +
            8 * zStar ^ 2 - 10)) /
          (2 * (zStar ^ 5 + zStar ^ 4 + 2 * zStar + 3) *
            (2 * zStar ^ 8 + 2 * zStar ^ 7 - 2 * zStar ^ 4 - 2 * zStar ^ 3 +
              4 * zStar ^ 2 - 5)) ∧
      591108823804 * cStar ^ 8 + 2774731980032 * cStar ^ 7 - 1469915176888 * cStar ^ 6 +
          2634492313776 * cStar ^ 5 + 1328731569804 * cStar ^ 4 + 269235674452 * cStar ^ 3 -
          5203293312 * cStar ^ 2 - 1491753550 * cStar - 268515639 ≠ 0 := by
  dsimp
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num
  · norm_num

end Omega.POM
