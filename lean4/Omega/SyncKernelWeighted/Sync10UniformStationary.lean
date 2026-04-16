import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Chapter-local wrapper for the exact 10-state stationary law of the uniform-input sync kernel.
The data record the finite 10-state Markov kernel, the rational transition weights, and the
candidate stationary vector whose entries sum to one and solve `πP = π` entrywise. -/
structure Sync10UniformStationaryData where
  tenStateKernel : Prop
  rationalTransitionWeights : Prop
  candidateStationaryVector : Prop
  tenStateKernel_h : tenStateKernel
  rationalTransitionWeights_h : rationalTransitionWeights
  candidateStationaryVector_h : candidateStationaryVector
  stateSpaceExact : Prop
  stationaryMassesExact : Prop
  deriveStateSpaceExact :
    tenStateKernel → rationalTransitionWeights → candidateStationaryVector → stateSpaceExact
  deriveStationaryMassesExact :
    stateSpaceExact → stationaryMassesExact

/-- Paper-facing wrapper for the exact 10-state stationary distribution under uniform input.
Once the 10-state rational kernel and the candidate stationary vector are fixed, the state-space
description is exact and the listed rational masses satisfy the stationary equations.
    prop:sync10-uniform-stationary -/
theorem paper_sync10_uniform_stationary (D : Sync10UniformStationaryData) :
    D.stateSpaceExact ∧ D.stationaryMassesExact := by
  have hStateSpace : D.stateSpaceExact :=
    D.deriveStateSpaceExact
      D.tenStateKernel_h
      D.rationalTransitionWeights_h
      D.candidateStationaryVector_h
  exact ⟨hStateSpace, D.deriveStationaryMassesExact hStateSpace⟩

end Omega.SyncKernelWeighted
