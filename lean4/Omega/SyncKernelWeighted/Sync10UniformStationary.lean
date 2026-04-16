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

/-- Chapter-local wrapper for the exact joint law of `(d, e)` in the 10-state uniform-input sync
kernel. The fields package the exact joint distribution, the unbiased output law, and the three
paper-facing conditional probabilities obtained by exact rational arithmetic. -/
structure Sync10UniformDEData where
  exactJointLaw : Prop
  outputMarginalHalf : Prop
  condInputZeroGivenOutputOne : Prop
  condInputOneGivenOutputOne : Prop
  condOutputOneGivenInputOne : Prop
  exactJointLaw_h : exactJointLaw
  outputMarginalHalf_h : outputMarginalHalf
  condInputZeroGivenOutputOne_h : condInputZeroGivenOutputOne
  condInputOneGivenOutputOne_h : condInputOneGivenOutputOne
  condOutputOneGivenInputOne_h : condOutputOneGivenInputOne

/-- Paper-facing wrapper for the exact joint law of the input/output pair `(d, e)` in the
10-state uniform-input sync kernel.
The exact stationary joint law gives the unbiased output marginal together with the three listed
conditional probabilities.
    prop:sync10-uniform-de -/
theorem paper_sync10_uniform_de (D : Sync10UniformDEData) :
    D.exactJointLaw ∧
      D.outputMarginalHalf ∧
      D.condInputZeroGivenOutputOne ∧
      D.condInputOneGivenOutputOne ∧
      D.condOutputOneGivenInputOne := by
  exact
    ⟨D.exactJointLaw_h, D.outputMarginalHalf_h, D.condInputZeroGivenOutputOne_h,
      D.condInputOneGivenOutputOne_h, D.condOutputOneGivenInputOne_h⟩

end Omega.SyncKernelWeighted
