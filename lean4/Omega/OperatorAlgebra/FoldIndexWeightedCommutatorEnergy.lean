import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldJonesCommutatorRank2Spectrum

namespace Omega.OperatorAlgebra

open scoped BigOperators
open FoldJonesCommutatorRank2SpectrumData

/-- Concrete finite-fiber data for the index-weighted commutator energy identity. -/
structure FoldIndexWeightedCommutatorEnergyData extends FoldJonesCommutatorRank2SpectrumData

namespace FoldIndexWeightedCommutatorEnergyData

/-- The Jones-index weighted Hilbert-Schmidt norm squared of the commutator blocks. -/
def indexWeightedHsNormSq (D : FoldIndexWeightedCommutatorEnergyData) : ℝ :=
  D.toFoldJonesCommutatorRank2SpectrumData.indexWeightedHSSquared

/-- The fiberwise residual `L²` energy. -/
def residualL2Energy (D : FoldIndexWeightedCommutatorEnergyData) : ℝ :=
  ∑ x, (D.fiberSize x : ℝ) * D.variance x ^ 2

end FoldIndexWeightedCommutatorEnergyData

open FoldIndexWeightedCommutatorEnergyData

/-- Paper label: `prop:op-algebra-fold-index-weighted-commutator-energy`.
This is the normalized form of the audited index-weighted Hilbert-Schmidt identity from the
rank-two Jones commutator block decomposition. -/
theorem paper_op_algebra_fold_index_weighted_commutator_energy
    (D : FoldIndexWeightedCommutatorEnergyData) :
    (1 / 2 : ℝ) * D.indexWeightedHsNormSq = D.residualL2Energy := by
  have hhs :
      D.toFoldJonesCommutatorRank2SpectrumData.indexWeightedHSSquared =
        2 * ∑ x, (D.fiberSize x : ℝ) * D.variance x ^ 2 :=
    (paper_op_algebra_fold_jones_commutator_rank2_spectrum
      D.toFoldJonesCommutatorRank2SpectrumData).2.2.2
  unfold FoldIndexWeightedCommutatorEnergyData.indexWeightedHsNormSq
    FoldIndexWeightedCommutatorEnergyData.residualL2Energy
  rw [hhs]
  ring

end Omega.OperatorAlgebra
