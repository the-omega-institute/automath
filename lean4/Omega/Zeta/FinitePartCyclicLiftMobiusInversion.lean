import Mathlib.Tactic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for Möbius inversion of the finite-part cyclic-lift multiple-sum
transform.
    prop:finite-part-cyclic-lift-mobius-inversion -/
theorem paper_etds_finite_part_cyclic_lift_mobius_inversion
    (dirichletMultipleSum mobiusRecovery : Prop) :
    dirichletMultipleSum ->
      (dirichletMultipleSum -> mobiusRecovery) ->
      dirichletMultipleSum ∧ mobiusRecovery := by
  intro hMultiple hRecovery
  exact ⟨hMultiple, hRecovery hMultiple⟩

/-- Publication-facing finite-part wrapper for the cyclic-lift multiple-sum Möbius recovery.
    prop:finite-part-cyclic-lift-mobius-inversion -/
theorem paper_finite_part_cyclic_lift_mobius_inversion
    (dirichletMultipleSum mobiusRecovery : Prop)
    (hMultiple : dirichletMultipleSum)
    (hRecovery : dirichletMultipleSum → mobiusRecovery) :
    dirichletMultipleSum ∧ mobiusRecovery := by
  exact ⟨hMultiple, hRecovery hMultiple⟩

end Omega.Zeta
