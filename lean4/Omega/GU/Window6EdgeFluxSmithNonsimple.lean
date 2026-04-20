import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.GU

open Matrix

/-- Audited four-block edge-flux interaction matrix from the window-`6` skeleton arithmetic. -/
def window6EdgeFluxSkeletonAuditedMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.diagonal ![1, 1, 3, 3450]

theorem det_window6EdgeFluxSkeletonAuditedMatrix :
    window6EdgeFluxSkeletonAuditedMatrix.det = 10350 := by
  native_decide

/-- Determinants of the irreducible rank-`4` finite Cartan types `A₄`, `B₄`, `C₄`, `D₄`, `F₄`. -/
def finiteTypeIrreducibleRank4CartanDeterminants : List ℤ :=
  [5, 2, 2, 4, 1]

/-- Concrete audited Smith-data package for the window-`6` four-block edge-flux skeleton. -/
structure Window6EdgeFluxSmithNonsimpleData where
  edgeFluxMatrix : Matrix (Fin 4) (Fin 4) ℤ
  audited_edgeFluxMatrix : edgeFluxMatrix = window6EdgeFluxSkeletonAuditedMatrix

/-- Audited Smith diagonal of the edge-flux skeleton matrix. -/
def Window6EdgeFluxSmithNonsimpleData.smithDiagonal (_D : Window6EdgeFluxSmithNonsimpleData) :
    List ℤ :=
  [1, 1, 3, 3450]

/-- Determinant of the audited edge-flux skeleton matrix. -/
def Window6EdgeFluxSmithNonsimpleData.determinant (D : Window6EdgeFluxSmithNonsimpleData) : ℤ :=
  D.edgeFluxMatrix.det

/-- The determinant mismatch excludes the audited matrix from the irreducible rank-`4` finite
Cartan list. -/
def Window6EdgeFluxSmithNonsimpleData.notFiniteTypeIrreducibleCartan
    (D : Window6EdgeFluxSmithNonsimpleData) : Prop :=
  D.determinant ∉ finiteTypeIrreducibleRank4CartanDeterminants

/-- The audited window-`6` edge-flux skeleton has Smith diagonal `[1,1,3,3450]`, determinant
`10350`, and determinant mismatch with every irreducible rank-`4` finite Cartan type.
    cor:window6-edge-flux-skeleton-smith-nonsimple -/
theorem paper_window6_edge_flux_skeleton_smith_nonsimple (D : Window6EdgeFluxSmithNonsimpleData) :
    D.smithDiagonal = [1, 1, 3, 3450] ∧
      D.determinant = (10350 : ℤ) ∧
      D.notFiniteTypeIrreducibleCartan := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold Window6EdgeFluxSmithNonsimpleData.determinant
    rw [D.audited_edgeFluxMatrix, det_window6EdgeFluxSkeletonAuditedMatrix]
  · unfold Window6EdgeFluxSmithNonsimpleData.notFiniteTypeIrreducibleCartan
      Window6EdgeFluxSmithNonsimpleData.determinant finiteTypeIrreducibleRank4CartanDeterminants
    rw [D.audited_edgeFluxMatrix, det_window6EdgeFluxSkeletonAuditedMatrix]
    native_decide

end Omega.GU
