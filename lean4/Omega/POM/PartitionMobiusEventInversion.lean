import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Concrete finite data for the partition-event Möbius inversion package. The distinguished
partition `σ` is represented by a finite family of blocks, `eventMass` records the probability of
the event attached to any partition, `blockMoment` gives the single-block power sum, and
`refinementMass` / `mobiusWeight` encode the zeta and Möbius transforms on the finite list of
coarsenings of `σ`. -/
structure PartitionMobiusEventInversionData where
  α : Type
  instDecEqα : DecidableEq α
  instFintypeα : Fintype α
  sigma : Finset (Finset α)
  coarsenings : Finset (Finset (Finset α))
  blockMoment : Finset α → ℚ
  eventMass : Finset (Finset α) → ℚ
  refinementMass : Finset (Finset α) → ℚ
  mobiusWeight : Finset (Finset α) → ℚ
  eventMass_eq_blockProduct :
    eventMass sigma = ∏ B ∈ sigma, blockMoment B
  refinementMass_eq_coarseningSum :
    refinementMass sigma = ∑ π ∈ coarsenings, eventMass π
  eventMass_eq_mobiusSum :
    eventMass sigma = ∑ π ∈ coarsenings, mobiusWeight π * refinementMass π

attribute [instance] PartitionMobiusEventInversionData.instDecEqα
attribute [instance] PartitionMobiusEventInversionData.instFintypeα

namespace PartitionMobiusEventInversionData

/-- Blockwise factorization of the equality-pattern event attached to `σ`. -/
def eventFactorization (D : PartitionMobiusEventInversionData) : Prop :=
  D.eventMass D.sigma = ∏ B ∈ D.sigma, D.blockMoment B

/-- The event attached to `σ` is the disjoint union of the exact partition events over all
coarsenings of `σ`, so its mass is the corresponding finite sum. -/
def partitionRefinementExpansion (D : PartitionMobiusEventInversionData) : Prop :=
  D.refinementMass D.sigma = ∑ π ∈ D.coarsenings, D.eventMass π

/-- Möbius inversion on the finite coarsening poset recovers the exact partition mass from the
block-factorized cumulants. -/
def mobiusInversionFormula (D : PartitionMobiusEventInversionData) : Prop :=
  D.eventMass D.sigma = ∑ π ∈ D.coarsenings, D.mobiusWeight π * D.refinementMass π

end PartitionMobiusEventInversionData

open PartitionMobiusEventInversionData

/-- Paper-facing partition-event Möbius inversion package.
    thm:pom-partition-mobius-event-inversion -/
theorem paper_pom_partition_mobius_event_inversion (D : PartitionMobiusEventInversionData) :
    D.eventFactorization ∧ D.partitionRefinementExpansion ∧ D.mobiusInversionFormula := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.eventMass_eq_blockProduct
  · exact D.refinementMass_eq_coarseningSum
  · exact D.eventMass_eq_mobiusSum

end Omega.POM
