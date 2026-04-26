import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Conclusion.GoldenSprtOnebitAncillary

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `cor:conclusion-golden-sprt-clock-is-pure-resource`. Once the stopped sample has
collapsed to the terminal sign, the stopping clock carries no additional information and its
posterior error is the deterministic threshold constant. -/
def conclusion_golden_sprt_clock_is_pure_resource_statement
    (D : GoldenSprtOnebitAncillaryData) : Prop :=
  D.Holds ∧ D.errorProb = 1 / (1 + Real.goldenRatio ^ D.T)

/-- Paper label: `cor:conclusion-golden-sprt-clock-is-pure-resource`. The one-bit ancillary
package already records that the clock contributes no extra inference content, and the stopping
error is exactly the threshold-dependent posterior constant. -/
theorem paper_conclusion_golden_sprt_clock_is_pure_resource
    (D : GoldenSprtOnebitAncillaryData) :
    conclusion_golden_sprt_clock_is_pure_resource_statement D := by
  exact ⟨paper_conclusion_golden_sprt_onebit_ancillary D, rfl⟩

end

end Omega.Conclusion
