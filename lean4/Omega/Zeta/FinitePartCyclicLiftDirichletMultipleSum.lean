import Omega.Zeta.FinitePartCyclicLiftReducedConstantClosed

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cyclic-lift multiple-sum expansion in the ETDS
finite-part section.
    prop:finite-part-cyclic-lift-dirichlet-multiple-sum -/
theorem paper_etds_finite_part_cyclic_lift_dirichlet_multiple_sum
    (reducedConstantClosed dirichletMultipleSum tailBound : Prop)
    (hClosed : reducedConstantClosed)
    (hClosedToMultipleSum : reducedConstantClosed → dirichletMultipleSum)
    (hMultipleToTail : dirichletMultipleSum → tailBound) :
    dirichletMultipleSum ∧ tailBound := by
  have hMultiple : dirichletMultipleSum := hClosedToMultipleSum hClosed
  exact ⟨hMultiple, hMultipleToTail hMultiple⟩

end Omega.Zeta
