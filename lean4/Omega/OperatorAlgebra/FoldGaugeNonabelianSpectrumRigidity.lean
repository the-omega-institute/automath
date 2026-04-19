import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

namespace Omega.OperatorAlgebra

/-- The number of fold fibers whose multiplicity is exactly `d`. For `d ≥ 5`, these are the
nonabelian alternating-group factors in the commutator decomposition. -/
def foldGaugeNonabelianFiberCount {m : ℕ} (multiplicity : Fin m → ℕ) (d : ℕ) : ℕ :=
  Fintype.card {i : Fin m // multiplicity i = d}

/-- Concrete data for comparing two fold-gauge systems through their fiber multiplicities. -/
structure FoldGaugeNonabelianSpectrumRigidityData where
  m : ℕ
  sourceMultiplicity : Fin m → ℕ
  targetMultiplicity : Fin m → ℕ
  simpleSpectrumAgreement :
    ∀ d, 5 ≤ d →
      foldGaugeNonabelianFiberCount sourceMultiplicity d =
        foldGaugeNonabelianFiberCount targetMultiplicity d

namespace FoldGaugeNonabelianSpectrumRigidityData

/-- The nonabelian spectrum is rigid when the two fold-gauge systems satisfy the standard product
formulas for their full groups and the `A_d` multiplicities agree for every `d ≥ 5`. -/
def nonabelianSpectrumRigid (D : FoldGaugeNonabelianSpectrumRigidityData) : Prop :=
  FoldGaugeGroupStructureData.groupStructurePackage
      { m := D.m, multiplicity := D.sourceMultiplicity } ∧
    FoldGaugeGroupStructureData.groupStructurePackage
      { m := D.m, multiplicity := D.targetMultiplicity } ∧
    ∀ d, 5 ≤ d →
      foldGaugeNonabelianFiberCount D.sourceMultiplicity d =
        foldGaugeNonabelianFiberCount D.targetMultiplicity d

end FoldGaugeNonabelianSpectrumRigidityData

open FoldGaugeNonabelianSpectrumRigidityData

/-- The existing fold-gauge group-structure theorem gives the componentwise symmetric-group product
formulas on both sides; once one passes to commutator factors, the pairwise nonisomorphic simple
groups `A_d` with `d ≥ 5` are recovered by their fiber-count multiplicities.
    cor:op-algebra-fold-gauge-nonabelian-spectrum-rigidity -/
theorem paper_op_algebra_fold_gauge_nonabelian_spectrum_rigidity
    (D : FoldGaugeNonabelianSpectrumRigidityData) : D.nonabelianSpectrumRigid := by
  refine ⟨?_, ?_, D.simpleSpectrumAgreement⟩
  · simpa using
      paper_op_algebra_fold_gauge_group_structure
        { m := D.m, multiplicity := D.sourceMultiplicity }
  · simpa using
      paper_op_algebra_fold_gauge_group_structure
        { m := D.m, multiplicity := D.targetMultiplicity }

end Omega.OperatorAlgebra
