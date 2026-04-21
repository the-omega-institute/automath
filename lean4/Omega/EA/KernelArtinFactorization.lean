import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.EA.KernelPeterWeylBlockDiagonalization

namespace Omega.EA

open Matrix
open Omega.Conclusion.FoldbinGroupoidTracialSimplex

/-- Concrete one-dimensional Artin block. -/
def kernelArtinScalarBlock (u : ℚ) : Matrix (Fin 1) (Fin 1) ℚ :=
  !![u]

/-- Concrete two-dimensional Artin block, acting by scalar right-multiplication on a `2`-channel.
-/
def kernelArtinVectorBlock (v : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![v, 0; 0, v]

/-- Concrete regular block obtained by stacking the scalar and vector channels. -/
def kernelArtinRegularBlock (u v : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![u, 0, 0;
    0, v, 0;
    0, 0, v]

/-- Determinant of the regular Artin block. -/
def kernelArtinRegularDet (t u v : ℚ) : ℚ :=
  Matrix.det (1 - t • kernelArtinRegularBlock u v)

/-- Determinant of the scalar Artin block. -/
def kernelArtinScalarDet (t u : ℚ) : ℚ :=
  Matrix.det (1 - t • kernelArtinScalarBlock u)

/-- Determinant of the two-dimensional Artin block. -/
def kernelArtinVectorDet (t v : ℚ) : ℚ :=
  Matrix.det (1 - t • kernelArtinVectorBlock v)

/-- Inverse-determinant zeta factor attached to the regular block. -/
def kernelArtinRegularZeta (t u v : ℚ) : ℚ :=
  (kernelArtinRegularDet t u v)⁻¹

/-- Inverse-determinant zeta factor attached to the scalar block. -/
def kernelArtinScalarZeta (t u : ℚ) : ℚ :=
  (kernelArtinScalarDet t u)⁻¹

/-- Inverse-determinant zeta factor attached to the two-dimensional block. -/
def kernelArtinVectorZeta (t v : ℚ) : ℚ :=
  (kernelArtinVectorDet t v)⁻¹

/-- The Peter--Weyl block witness imported from the AF-stage wrapper. -/
def kernelArtinPeterWeylWitness (m : ℕ) : Prop :=
  (∑ x : foldGroupoidAFStage m, (Omega.X.fiberMultiplicity x) ^ 2 = Omega.momentSum 2 m) ∧
    (∑ x : foldGroupoidAFStage m, Omega.X.fiberMultiplicity x = 2 ^ m) ∧
    foldGroupoidHolographicTrace m ∈ tracialSimplex (ι := foldGroupoidAFStage m)

/-- Determinant form of the finite Artin factorization: the Peter--Weyl block witness is retained,
and the regular determinant splits as the product of the scalar and two-dimensional channels. -/
def kernelArtinDetFactorization (m : ℕ) (t u v : ℚ) : Prop :=
  kernelArtinPeterWeylWitness m ∧
    kernelArtinRegularDet t u v = kernelArtinScalarDet t u * kernelArtinVectorDet t v

/-- Zeta form of the same factorization, valid once the three determinants are invertible. -/
def kernelArtinZetaFactorization (t u v : ℚ) : Prop :=
  kernelArtinRegularDet t u v ≠ 0 →
    kernelArtinScalarDet t u ≠ 0 →
      kernelArtinVectorDet t v ≠ 0 →
        kernelArtinRegularZeta t u v = kernelArtinScalarZeta t u * kernelArtinVectorZeta t v

private theorem kernelArtin_det_identity (t u v : ℚ) :
    kernelArtinRegularDet t u v = kernelArtinScalarDet t u * kernelArtinVectorDet t v := by
  simp [kernelArtinRegularDet, kernelArtinScalarDet, kernelArtinVectorDet, kernelArtinRegularBlock,
    kernelArtinScalarBlock, kernelArtinVectorBlock, Matrix.det_fin_two, Matrix.det_fin_three]
  ring

private theorem kernelArtin_zeta_identity (t u v : ℚ) :
    kernelArtinZetaFactorization t u v := by
  intro _hreg hscalar hvector
  unfold kernelArtinRegularZeta kernelArtinScalarZeta kernelArtinVectorZeta
  rw [kernelArtin_det_identity]
  field_simp [kernelArtinScalarDet, kernelArtinVectorDet, hscalar, hvector]

/-- Finite Artin factorization for the concrete Peter--Weyl block surrogate: the imported AF-stage
block witness provides the channel decomposition, the regular determinant factors into the
one-dimensional and two-dimensional blocks, and the zeta identity is the inverse-determinant
corollary.
    prop:kernel-artin-factorization -/
theorem paper_kernel_artin_factorization (m : ℕ) (t u v : ℚ) :
    kernelArtinDetFactorization m t u v ∧ kernelArtinZetaFactorization t u v := by
  have hPW : kernelArtinPeterWeylWitness m := paper_kernel_peter_weyl_block_diagonalization m
  exact ⟨⟨hPW, kernelArtin_det_identity t u v⟩, kernelArtin_zeta_identity t u v⟩

end Omega.EA
