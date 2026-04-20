import Mathlib.Tactic
import Omega.Folding.CollisionKernel
import Omega.Folding.CollisionZeta

namespace Omega.POM

/-- Paper-facing wrapper for the explicit five-state `S₅` realization, its exact order-5
recurrence, the Perron-root asymptotic, and the resulting entropy formula.
    prop:pom-s5-recurrence -/
theorem paper_pom_s5_recurrence (explicitS5Realization exactS5Recurrence s5Asymptotic
    entropyFormula : Prop) (hRealize : explicitS5Realization)
    (hRec : explicitS5Realization → exactS5Recurrence)
    (hAsymp : exactS5Recurrence → s5Asymptotic)
    (hEntropy : s5Asymptotic → entropyFormula) :
    explicitS5Realization ∧ exactS5Recurrence ∧ s5Asymptotic ∧ entropyFormula := by
  refine ⟨hRealize, hRec hRealize, hAsymp (hRec hRealize), ?_⟩
  exact hEntropy (hAsymp (hRec hRealize))

end Omega.POM
