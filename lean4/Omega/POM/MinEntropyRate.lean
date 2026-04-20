import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- Min-entropy-rate endpoint for the folded-output max-fiber asymptotic. -/
noncomputable def minEntropyRate : ℝ :=
  Real.log 2 - Real.log ((1 + Real.sqrt 5) / 2) / 2

/-- Closed-form endpoint value of the min-entropy-rate constant.
    cor:pom-min-entropy-rate -/
theorem paper_pom_min_entropy_rate :
    minEntropyRate = Real.log 2 - Real.log ((1 + Real.sqrt 5) / 2) / 2 := by
  rfl

end Omega.POM
