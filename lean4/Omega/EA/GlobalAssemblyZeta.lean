import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.EA.CarryFreeZetaTrichotomy

namespace Omega.EA

open Polynomial
open Omega.Graph

/-- Global carry-free assembly for the `K9` one-state branch. -/
def globalAssemblyK9Adjacency : Matrix (Fin 1) (Fin 1) ℤ :=
  sevenShiftAdjacency

/-- Global carry-free assembly for the `K13` one-state branch. -/
def globalAssemblyK13Adjacency : Matrix (Fin 1) (Fin 1) ℤ :=
  threeShiftAdjacency

/-- Global carry-free assembly for the `K21` branch, obtained from the tensor-square collapse of
the golden-mean adjacency. -/
def globalAssemblyK21Adjacency : Matrix (Fin 2) (Fin 2) ℤ :=
  goldenMeanAdjacency ^ 2

/-- Paper-facing zeta package for the three global assembly cases. -/
abbrev globalAssemblyZetaStatement : Prop :=
  globalAssemblyK9Adjacency.charpoly = Polynomial.X - Polynomial.C 7 ∧
    globalAssemblyK13Adjacency.charpoly = Polynomial.X - Polynomial.C 3 ∧
    globalAssemblyK21Adjacency.charpoly = Polynomial.X ^ 2 - 3 * Polynomial.X + 1

private lemma globalAssemblyK21Adjacency_eq :
    globalAssemblyK21Adjacency = !![2, 1; 1, 1] := by
  unfold globalAssemblyK21Adjacency
  native_decide

private lemma globalAssemblyK21Adjacency_trace :
    globalAssemblyK21Adjacency.trace = 3 := by
  rw [globalAssemblyK21Adjacency_eq]
  native_decide

private lemma globalAssemblyK21Adjacency_det :
    globalAssemblyK21Adjacency.det = 1 := by
  rw [globalAssemblyK21Adjacency_eq]
  native_decide

private lemma globalAssemblyK21Adjacency_charpoly :
    globalAssemblyK21Adjacency.charpoly = Polynomial.X ^ 2 - 3 * Polynomial.X + 1 := by
  rw [Matrix.charpoly_fin_two, globalAssemblyK21Adjacency_trace, globalAssemblyK21Adjacency_det]
  norm_num

/-- The global carry-free assemblies inherit the one-state `K9` and `K13` zeta factors from the
single-flow audit, while the `K21` factor is the tensor-square golden-mean determinant
`X² - 3X + 1`.
    cor:global-assembly-zeta -/
theorem paper_global_assembly_zeta : globalAssemblyZetaStatement := by
  rcases paper_carry_free_zeta_trichotomy with ⟨_, _, _, hK9, hK13, _⟩
  refine ⟨?_, ?_, globalAssemblyK21Adjacency_charpoly⟩
  · simpa [globalAssemblyK9Adjacency] using hK9
  · simpa [globalAssemblyK13Adjacency] using hK13

end Omega.EA
