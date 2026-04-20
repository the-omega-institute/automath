import Mathlib.Tactic
import Omega.Folding.FoldMultiplicityGroupAlgebra

namespace Omega.Folding

/-- Concrete window-free data for the group-ring constant-term presentation of the fold-fiber bias
energy. The only parameter is the ambient fold length `m`; all paper-facing propositions are then
defined from the existing fold-multiplicity subset-product package. -/
structure FoldFiberBiasEnergyGroupringConstantTermData where
  m : ℕ

namespace FoldFiberBiasEnergyGroupringConstantTermData

/-- The cyclic modulus attached to fold multiplicities. -/
def modulus (D : FoldFiberBiasEnergyGroupringConstantTermData) : ℕ :=
  foldMultiplicityModulus D.m

/-- The distinguished zero residue class. -/
def zeroResidue (D : FoldFiberBiasEnergyGroupringConstantTermData) : Fin D.modulus :=
  ⟨0, foldMultiplicityModulus_pos D.m⟩

/-- The zero-residue multiplicity, viewed as the constant term of the group-ring expansion. -/
def constantCoefficient (D : FoldFiberBiasEnergyGroupringConstantTermData) : ℕ :=
  foldMultiplicityGeneratingPolynomial D.m D.zeroResidue

/-- The same quantity extracted directly from the expanded subset product. -/
def subsetProductConstantCoefficient (D : FoldFiberBiasEnergyGroupringConstantTermData) : ℕ :=
  foldMultiplicitySubsetProductCoeff D.m D.zeroResidue

/-- Clearing the cyclic-average denominator produces an integer numerator for the energy. -/
def energyNumerator (D : FoldFiberBiasEnergyGroupringConstantTermData) : ℕ :=
  D.modulus * D.constantCoefficient

/-- The constant term of the fold-fiber bias energy is the zero-residue coefficient in the
cyclic group ring. -/
def constantTermFormula (D : FoldFiberBiasEnergyGroupringConstantTermData) : Prop :=
  D.constantCoefficient = D.subsetProductConstantCoefficient

/-- The cyclic modulus divides the cleared energy numerator. -/
def energyDenominatorDivides (D : FoldFiberBiasEnergyGroupringConstantTermData) : Prop :=
  D.modulus ∣ D.energyNumerator

end FoldFiberBiasEnergyGroupringConstantTermData

open FoldFiberBiasEnergyGroupringConstantTermData

/-- Paper label: `cor:fold-fiber-bias-energy-groupring-constant-term`. -/
theorem paper_fold_fiber_bias_energy_groupring_constant_term
    (D : FoldFiberBiasEnergyGroupringConstantTermData) :
    D.constantTermFormula ∧ D.energyDenominatorDivides := by
  refine ⟨?_, ?_⟩
  · simpa [FoldFiberBiasEnergyGroupringConstantTermData.constantTermFormula,
      FoldFiberBiasEnergyGroupringConstantTermData.constantCoefficient,
      FoldFiberBiasEnergyGroupringConstantTermData.subsetProductConstantCoefficient] using
      (paper_fold_multiplicity_group_algebra D.m) D.zeroResidue
  · refine ⟨D.constantCoefficient, ?_⟩
    simp [FoldFiberBiasEnergyGroupringConstantTermData.energyNumerator]

end Omega.Folding
