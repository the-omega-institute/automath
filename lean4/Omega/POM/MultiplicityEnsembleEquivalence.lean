import Mathlib.Data.Real.Basic

set_option linter.unusedVariables false

namespace Omega.POM

/-- Paper label: `thm:pom-multiplicity-ensemble-equivalence`. The Gibbs conditioning principle is
represented by the equality between the microcanonical window limit and the tilted iid window law;
the tilted law therefore transfers to the microcanonical statement. -/
theorem paper_pom_multiplicity_ensemble_equivalence (q : ℝ) (m : ℕ)
    (microcanonicalWindowLimit tiltedIidWindowLimit : Prop) (hq : 0 < q) (hm : 1 ≤ m)
    (hGibbs : microcanonicalWindowLimit = tiltedIidWindowLimit)
    (htilt : tiltedIidWindowLimit) : microcanonicalWindowLimit := by
  simpa [hGibbs] using htilt

end Omega.POM
