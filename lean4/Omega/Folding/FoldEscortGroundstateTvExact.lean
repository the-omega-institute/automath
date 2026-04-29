import Mathlib.Analysis.SpecialFunctions.Exp
import Omega.Conclusion.FrozenEscortTvRigidity

namespace Omega.Folding

/-- The folding-level escort/groundstate TV formula is exactly the chapter-level frozen-escort
rigidity statement instantiated with the packaged finite data.
    thm:fold-escort-groundstate-tv-exact -/
theorem paper_fold_escort_groundstate_tv_exact
    (h : Omega.Conclusion.FrozenEscortTvRigidityData) :
    h.tvDistance = 1 - h.massOnMaxFiber ∧ h.tvDistance ≤ Real.exp (-h.exponentialGap) := by
  simpa using Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity h

end Omega.Folding
