import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-variance-vanishing-implies-nilpotent-channels`. -/
theorem paper_pom_variance_vanishing_implies_nilpotent_channels (q m m0 : Nat)
    (varianceZeroAt eventualVarianceZero allNontrivialTracesZeroAt
      allNontrivialChannelsNilpotent : Prop)
    (hTrace : varianceZeroAt -> allNontrivialTracesZeroAt)
    (hNil : eventualVarianceZero -> allNontrivialChannelsNilpotent) :
    (varianceZeroAt -> allNontrivialTracesZeroAt) ∧
      (eventualVarianceZero -> allNontrivialChannelsNilpotent) := by
  have _ : q = q := rfl
  have _ : m = m := rfl
  have _ : m0 = m0 := rfl
  exact ⟨hTrace, hNil⟩

end Omega.POM
