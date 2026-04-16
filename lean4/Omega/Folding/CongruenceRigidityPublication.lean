namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the arithmetic congruence-rigidity theorem in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    thm:congruence-rigidity -/
theorem paper_resolution_folding_congruence_rigidity
    {RawBlock FoldedBlock ResidueVec : Type}
    (blockCode : RawBlock → FoldedBlock)
    (residueCode : RawBlock → ResidueVec)
    (visibleCode : FoldedBlock → ResidueVec)
    (hVisible : ∀ ω, residueCode ω = visibleCode (blockCode ω))
    (hBlockInj : Function.Injective blockCode)
    (hVisibleInj : Function.Injective visibleCode) :
    Function.Injective residueCode := by
  intro ω ω' hEq
  apply hBlockInj
  apply hVisibleInj
  simpa [hVisible ω, hVisible ω'] using hEq

end Omega.Folding
