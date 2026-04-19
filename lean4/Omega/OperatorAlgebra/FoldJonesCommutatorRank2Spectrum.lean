import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace Omega.OperatorAlgebra

/-- Finite fiber data for the rank-two Jones commutator package. The scalar `variance x` is the
common singular value on the `x`-fiber block, while `fiberSize x` is the corresponding Jones
index multiplicity. -/
structure FoldJonesCommutatorRank2SpectrumData where
  X : Type
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  instInhabitedX : Inhabited X
  variance : X → ℝ
  variance_nonneg : ∀ x, 0 ≤ variance x
  fiberSize : X → ℕ
  fiberSize_pos : ∀ x, 0 < fiberSize x

attribute [instance] FoldJonesCommutatorRank2SpectrumData.instDecEqX
attribute [instance] FoldJonesCommutatorRank2SpectrumData.instFintypeX
attribute [instance] FoldJonesCommutatorRank2SpectrumData.instInhabitedX

namespace FoldJonesCommutatorRank2SpectrumData

/-- The `2 × 2` fiber block modeling the off-diagonal Jones commutator on the constants plus
orthogonal-complement splitting. -/
def fiberBlock (D : FoldJonesCommutatorRank2SpectrumData) (x : D.X) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -(D.variance x); D.variance x, 0]

/-- The squared Hilbert-Schmidt norm of the `x`-fiber block. -/
def fiberHSSquared (D : FoldJonesCommutatorRank2SpectrumData) (x : D.X) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (D.fiberBlock x i j) ^ 2

/-- The global operator norm extracted from the fiberwise singular values. -/
def globalOperatorNorm (D : FoldJonesCommutatorRank2SpectrumData) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty D.variance

/-- The unweighted global Hilbert-Schmidt norm squared. -/
def globalHSSquared (D : FoldJonesCommutatorRank2SpectrumData) : ℝ :=
  ∑ x, D.fiberHSSquared x

/-- The Jones-index weighted Hilbert-Schmidt norm squared. -/
def indexWeightedHSSquared (D : FoldJonesCommutatorRank2SpectrumData) : ℝ :=
  ∑ x, (D.fiberSize x : ℝ) * D.fiberHSSquared x

/-- Every fiber block is off-diagonal relative to the constants plus orthogonal complement. -/
def fiberwiseBlockDecomposition (D : FoldJonesCommutatorRank2SpectrumData) : Prop :=
  ∀ x,
    D.fiberBlock x 0 0 = 0 ∧ D.fiberBlock x 1 1 = 0 ∧
      D.fiberBlock x 0 1 = -(D.variance x) ∧ D.fiberBlock x 1 0 = D.variance x

/-- The fiber block has equal singular-value square `σ(x)^2` on both basis vectors, and its
Hilbert-Schmidt norm is `2 σ(x)^2`. -/
def rankTwoSingularValueFormula (D : FoldJonesCommutatorRank2SpectrumData) : Prop :=
  ∀ x,
    Matrix.transpose (D.fiberBlock x) * D.fiberBlock x =
        (D.variance x) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      D.fiberHSSquared x = 2 * D.variance x ^ 2

/-- The operator norm is the maximum fiber variance and the global Hilbert-Schmidt norm is the
sum of the block contributions. -/
def globalNormFormula (D : FoldJonesCommutatorRank2SpectrumData) : Prop :=
  D.globalOperatorNorm = Finset.sup' Finset.univ Finset.univ_nonempty D.variance ∧
    D.globalHSSquared = 2 * ∑ x, D.variance x ^ 2

/-- The Jones-index weighted Hilbert-Schmidt norm inserts the fiber multiplicities `d_x`. -/
def indexWeightedHSFormula (D : FoldJonesCommutatorRank2SpectrumData) : Prop :=
  D.indexWeightedHSSquared = 2 * ∑ x, (D.fiberSize x : ℝ) * D.variance x ^ 2

lemma transpose_mul_fiberBlock (D : FoldJonesCommutatorRank2SpectrumData) (x : D.X) :
    Matrix.transpose (D.fiberBlock x) * D.fiberBlock x =
      (D.variance x) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiberBlock, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

lemma fiberHSSquared_eq (D : FoldJonesCommutatorRank2SpectrumData) (x : D.X) :
    D.fiberHSSquared x = 2 * D.variance x ^ 2 := by
  simp [fiberHSSquared, fiberBlock, Fin.sum_univ_two, pow_two]
  ring

end FoldJonesCommutatorRank2SpectrumData

open FoldJonesCommutatorRank2SpectrumData

/-- Paper-facing rank-two Jones commutator spectrum package.
    thm:op-algebra-fold-jones-commutator-rank2-spectrum -/
theorem paper_op_algebra_fold_jones_commutator_rank2_spectrum
    (D : FoldJonesCommutatorRank2SpectrumData) :
    D.fiberwiseBlockDecomposition ∧ D.rankTwoSingularValueFormula ∧ D.globalNormFormula ∧
      D.indexWeightedHSFormula := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp [FoldJonesCommutatorRank2SpectrumData.fiberBlock]
  · intro x
    exact ⟨D.transpose_mul_fiberBlock x, D.fiberHSSquared_eq x⟩
  · constructor
    · rfl
    · calc
        D.globalHSSquared = ∑ x, D.fiberHSSquared x := rfl
        _ = ∑ x, 2 * D.variance x ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact D.fiberHSSquared_eq x
        _ = 2 * ∑ x, D.variance x ^ 2 := by
              simpa using
                (Finset.mul_sum (s := Finset.univ) (a := (2 : ℝ))
                  (f := fun x => D.variance x ^ 2)).symm
  · calc
      D.indexWeightedHSSquared = ∑ x, (D.fiberSize x : ℝ) * D.fiberHSSquared x := rfl
      _ = ∑ x, (D.fiberSize x : ℝ) * (2 * D.variance x ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [D.fiberHSSquared_eq x]
      _ = ∑ x, 2 * ((D.fiberSize x : ℝ) * D.variance x ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
      _ = 2 * ∑ x, (D.fiberSize x : ℝ) * D.variance x ^ 2 := by
            simpa using
              (Finset.mul_sum (s := Finset.univ) (a := (2 : ℝ))
                (f := fun x => (D.fiberSize x : ℝ) * D.variance x ^ 2)).symm

end Omega.OperatorAlgebra
