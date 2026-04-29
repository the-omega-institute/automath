import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Folding.FoldFiberParityBiasRieszParsevalEnergy

open scoped BigOperators

namespace Omega.Folding

noncomputable section

/-- Concrete single-coordinate wrapper for the fold-fiber Fourier multiplier and Parseval energy
identity. The bias transform is the signed singleton Walsh coefficient extracted from the parity
package. -/
structure FoldFiberBiasFourierMultiplierEnergyData where
  parityData : FoldFiberParityBiasRieszParsevalEnergyData
  coordinate : Fin parityData.dimension

namespace FoldFiberBiasFourierMultiplierEnergyData

open FoldFiberParityBiasRieszParsevalEnergyData

def biasFourierTransform (D : FoldFiberBiasFourierMultiplierEnergyData) (t : ℕ) : ℂ :=
  -D.parityData.fourierTransform (D.parityData.singletonSigns D.coordinate) t

def biasEnergy (D : FoldFiberBiasFourierMultiplierEnergyData) : ℝ :=
  D.parityData.singleCoordinateEnergy D.coordinate

def multiplierFormula (D : FoldFiberBiasFourierMultiplierEnergyData) : Prop :=
  ∀ t,
    D.biasFourierTransform t =
      -(((2 : ℂ) ^ D.parityData.dimension)⁻¹ *
        Finset.prod Finset.univ
          (fun j : Fin D.parityData.dimension =>
            1 + (((if j = D.coordinate then (-1 : ℝ) else 1 : ℝ)) : ℂ) *
              D.parityData.coordinateCharacter t j))

def parsevalEnergyFormula (D : FoldFiberBiasFourierMultiplierEnergyData) : Prop :=
  D.biasEnergy =
    (D.parityData.modulus : ℝ)⁻¹ *
      Finset.sum (Finset.range D.parityData.modulus) (fun t => ‖D.biasFourierTransform t‖ ^ 2)

end FoldFiberBiasFourierMultiplierEnergyData

open FoldFiberBiasFourierMultiplierEnergyData
open FoldFiberParityBiasRieszParsevalEnergyData

/-- Paper label: `prop:fold-fiber-bias-fourier-multiplier-energy`. -/
theorem paper_fold_fiber_bias_fourier_multiplier_energy
    (D : FoldFiberBiasFourierMultiplierEnergyData) :
    D.multiplierFormula ∧ D.parsevalEnergyFormula := by
  refine ⟨?_, ?_⟩
  · intro t
    simp [FoldFiberBiasFourierMultiplierEnergyData.biasFourierTransform,
      FoldFiberParityBiasRieszParsevalEnergyData.fourierTransform,
      FoldFiberParityBiasRieszParsevalEnergyData.singletonSigns]
  · simp [FoldFiberBiasFourierMultiplierEnergyData.parsevalEnergyFormula,
    FoldFiberBiasFourierMultiplierEnergyData.biasEnergy,
    FoldFiberBiasFourierMultiplierEnergyData.biasFourierTransform,
    FoldFiberParityBiasRieszParsevalEnergyData.singleCoordinateEnergy,
    FoldFiberParityBiasRieszParsevalEnergyData.parsevalEnergy]

end

end Omega.Folding
