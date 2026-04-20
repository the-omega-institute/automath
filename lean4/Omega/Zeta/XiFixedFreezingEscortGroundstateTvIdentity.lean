import Omega.Conclusion.FrozenEscortTvRigidity

namespace Omega.Zeta

/-- The xi fixed-freezing escort/groundstate TV identity is exactly the chapter-level frozen-escort
rigidity package instantiated with the provided finite data.
    cor:xi-fixed-freezing-escort-groundstate-tv-identity -/
theorem paper_xi_fixed_freezing_escort_groundstate_tv_identity
    (h : Omega.Conclusion.FrozenEscortTvRigidityData) :
    h.tvDistance = 1 - h.massOnMaxFiber ∧ h.tvDistance ≤ Real.exp (-h.exponentialGap) := by
  simpa using Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity h

end Omega.Zeta
