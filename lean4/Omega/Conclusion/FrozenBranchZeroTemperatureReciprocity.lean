import Mathlib.Tactic
import Omega.Conclusion.FrozenBranchTwoScalarClosure

namespace Omega.Conclusion

noncomputable section

/-- The zero-temperature reciprocity rewrite expresses the frozen affine pressure branch using the
common frozen constant and the frozen entropy gap read from the unit samples `P(0)` and `P(1)`. -/
def conclusion_frozen_branch_zero_temperature_reciprocity_statement : Prop :=
  ∀ alphaStar gStar a : ℝ,
    let P := conclusion_frozen_branch_two_scalar_closure_pressure alphaStar gStar
    let alphaRecovered := (P 1 - P 0) / (1 - 0)
    let gRecovered := (1 * P 0 - 0 * P 1) / (1 - 0)
    P a =
      a *
          (conclusion_frozen_branch_two_scalar_closure_microMinEntropy alphaRecovered gRecovered a -
            conclusion_frozen_branch_two_scalar_closure_macroMinEntropy gRecovered a) +
        conclusion_frozen_branch_two_scalar_closure_macroMinEntropy gRecovered a

/-- Paper label: `thm:conclusion-frozen-branch-zero-temperature-reciprocity`. The frozen branch is
affine, the limiting entropy term collapses to the common frozen constant, and the pressure can be
rewritten using the entropy gap between the micro and macro frozen branches. -/
theorem paper_conclusion_frozen_branch_zero_temperature_reciprocity :
    conclusion_frozen_branch_zero_temperature_reciprocity_statement := by
  intro alphaStar gStar a
  simp [conclusion_frozen_branch_two_scalar_closure_pressure,
    conclusion_frozen_branch_two_scalar_closure_microMinEntropy,
    conclusion_frozen_branch_two_scalar_closure_macroMinEntropy]

end

end Omega.Conclusion
