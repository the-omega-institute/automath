import Omega.Folding.FoldFiberParityEnergySimplex

namespace Omega.Folding

noncomputable section

/-- Concrete fold-fiber bookkeeping for the erasure identity. The ambient collision law and the
erased law are read off from the existing slice-collision package, while the bias energy is the
quadratic parity-bias term. -/
structure FoldFiberBiasEnergyErasureData where
  sliceData : FoldFiberSliceCollisionData

namespace FoldFiberBiasEnergyErasureData

def biasEnergy (D : FoldFiberBiasEnergyErasureData) : ℚ :=
  D.sliceData.biasEnergy

def erasedCollisionProbability (D : FoldFiberBiasEnergyErasureData) : ℚ :=
  (D.sliceData.sliceCollisionZero + D.sliceData.sliceCollisionOne) / 2

def fullCollisionProbability (D : FoldFiberBiasEnergyErasureData) : ℚ :=
  D.sliceData.collisionProbability

end FoldFiberBiasEnergyErasureData

open FoldFiberBiasEnergyErasureData

/-- The erased collision law differs from the full collision law by exactly the fold-fiber
parity-bias energy.
    thm:fold-fiber-bias-energy-erasure-identity -/
theorem paper_fold_fiber_bias_energy_erasure_identity (D : FoldFiberBiasEnergyErasureData) :
    D.biasEnergy = D.erasedCollisionProbability - D.fullCollisionProbability := by
  simpa [FoldFiberBiasEnergyErasureData.biasEnergy,
    FoldFiberBiasEnergyErasureData.erasedCollisionProbability,
    FoldFiberBiasEnergyErasureData.fullCollisionProbability] using
    paper_fold_fiber_slice_collision_decomposition D.sliceData

end

end Omega.Folding
