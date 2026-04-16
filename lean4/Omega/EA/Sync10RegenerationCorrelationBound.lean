import Mathlib.Tactic

namespace Omega.EA

/-- Chapter-local package for the sync-10 regeneration/correlation corollary. The data store the
reset-word witness `00000`, the common-input coupling argument, and the two paper-facing
consequences: pathwise coalescence after the first reset block and the resulting total-variation
estimate. -/
structure Sync10RegenerationCorrelationBoundData where
  resetWordWitness : Prop
  commonInputCoupling : Prop
  pathwiseCoalescenceBound : Prop
  totalVariationBound : Prop
  resetWordWitness_h : resetWordWitness
  commonInputCoupling_h : commonInputCoupling
  derivePathwiseCoalescenceBound :
    resetWordWitness → commonInputCoupling → pathwiseCoalescenceBound
  deriveTotalVariationBound :
    pathwiseCoalescenceBound → totalVariationBound

/-- Paper-facing wrapper for the sync-10 regeneration/correlation bound: once the reset block
`00000` appears, the common-input coupling forces the two trajectories to agree five steps later,
and the total-variation estimate follows from the usual coupling characterization.
    cor:sync10-regeneration-correlation-bound -/
theorem paper_sync10_regeneration_correlation_bound
    (D : Sync10RegenerationCorrelationBoundData) :
    D.pathwiseCoalescenceBound ∧ D.totalVariationBound := by
  have hPathwise : D.pathwiseCoalescenceBound :=
    D.derivePathwiseCoalescenceBound D.resetWordWitness_h D.commonInputCoupling_h
  exact ⟨hPathwise, D.deriveTotalVariationBound hPathwise⟩

end Omega.EA
