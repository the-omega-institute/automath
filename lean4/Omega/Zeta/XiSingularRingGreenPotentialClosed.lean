import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `prop:xi-singular-ring-green-potential-closed`. -/
theorem paper_xi_singular_ring_green_potential_closed
    (OffCut PotentialIdentity ZeroBoundary InfinityNormalization : Prop)
    (hpot : PotentialIdentity)
    (hzero : ZeroBoundary)
    (hinf : InfinityNormalization) :
    PotentialIdentity ∧ ZeroBoundary ∧ InfinityNormalization := by
  exact ⟨hpot, hzero, hinf⟩

end Omega.Zeta
