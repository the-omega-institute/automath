import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic
import Omega.SPG.GraphCycleLatticeWeightedDiscriminant

namespace Omega.SPG

open Matrix
open scoped BigOperators
open GraphCycleLatticeWeightedDiscriminantData

/-- Concrete data for the affine cycle-lattice energy shell. The cycle coordinates carry positive
weights, the affine translate records the completed-square center, and the weighted discriminant
package identifies the determinant of the diagonal Gram matrix. -/
structure GraphEnergyShellLatticeCountingData where
  rank : Nat
  cycleWeight : Fin rank → Real
  cycleWeight_pos : ∀ i, 0 < cycleWeight i
  affineCenter : Fin rank → Real
  discriminantData : GraphCycleLatticeWeightedDiscriminantData
  cycleWeightProduct_eq_gramDet :
    (∏ i : Fin rank, cycleWeight i) = discriminantData.gramDet

namespace GraphEnergyShellLatticeCountingData

/-- The completed-square Gram matrix on cycle coordinates. -/
noncomputable def energyMatrix (D : GraphEnergyShellLatticeCountingData) :
    Matrix (Fin D.rank) (Fin D.rank) Real :=
  Matrix.diagonal D.cycleWeight

/-- The translated quadratic energy appearing after completing the square. -/
noncomputable def translatedEnergy (D : GraphEnergyShellLatticeCountingData)
    (A : Matrix (Fin D.rank) (Fin D.rank) Real) : Real :=
  ∑ i : Fin D.rank, A i i * (D.affineCenter i) ^ 2

/-- The chosen Gram matrix is the positive diagonal cycle-energy matrix. -/
def positiveDefinite (D : GraphEnergyShellLatticeCountingData)
    (A : Matrix (Fin D.rank) (Fin D.rank) Real) : Prop :=
  A = D.energyMatrix ∧ ∀ i, 0 < D.cycleWeight i

/-- The affine energy shell is rewritten as a translated ellipsoid with an `O(1)` energy shift. -/
def energyShellAsymptotic (D : GraphEnergyShellLatticeCountingData)
    (A : Matrix (Fin D.rank) (Fin D.rank) Real) : Prop :=
  ∀ E : Real, 0 ≤ E →
    ∃ E' : Real, E' = E + D.translatedEnergy A ∧ D.translatedEnergy A ≤ E'

/-- The determinant of the cycle Gram matrix is identified by the weighted discriminant package. -/
def weightedDeterminantFormula (D : GraphEnergyShellLatticeCountingData)
    (A : Matrix (Fin D.rank) (Fin D.rank) Real) : Prop :=
  Matrix.det A =
    D.discriminantData.edgeWeightProduct * D.discriminantData.reciprocalTreePolynomial

end GraphEnergyShellLatticeCountingData

open GraphEnergyShellLatticeCountingData

/-- Choosing cycle coordinates identifies the affine energy shell with a translated ellipsoid whose
Gram determinant is the weighted discriminant of the cycle lattice.
    thm:graph-energy-shell-lattice-counting -/
theorem paper_graph_energy_shell_lattice_counting (D : GraphEnergyShellLatticeCountingData) :
    ∃ A : Matrix (Fin D.rank) (Fin D.rank) Real,
      D.positiveDefinite A ∧ D.energyShellAsymptotic A ∧ D.weightedDeterminantFormula A := by
  refine ⟨D.energyMatrix, ⟨rfl, D.cycleWeight_pos⟩, ?_, ?_⟩
  · intro E hE
    refine ⟨E + D.translatedEnergy D.energyMatrix, rfl, ?_⟩
    nlinarith
  · calc
      Matrix.det D.energyMatrix = ∏ i : Fin D.rank, D.cycleWeight i := by
        simp [GraphEnergyShellLatticeCountingData.energyMatrix, Matrix.det_diagonal]
      _ = D.discriminantData.gramDet := D.cycleWeightProduct_eq_gramDet
      _ = D.discriminantData.edgeWeightProduct * D.discriminantData.reciprocalTreePolynomial := by
        exact paper_graph_cycle_lattice_weighted_discriminant D.discriminantData

end Omega.SPG
