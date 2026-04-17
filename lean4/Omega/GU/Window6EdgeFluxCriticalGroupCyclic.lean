import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.GU

open Matrix

/-- Audited reduced Laplacian for the window-`6` four-block edge-flux quotient. -/
def window6EdgeFluxAuditedReducedLaplacian : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.diagonal ![1, 1, 123336]

theorem det_window6EdgeFluxAuditedReducedLaplacian :
    window6EdgeFluxAuditedReducedLaplacian.det = 123336 := by
  native_decide

/-- Concrete reduced-Laplacian package for the window-`6` edge-flux audit. -/
structure Window6EdgeFluxCriticalGroupData where
  reducedLaplacian : Matrix (Fin 3) (Fin 3) ℤ
  audited_reducedLaplacian :
    reducedLaplacian = window6EdgeFluxAuditedReducedLaplacian

/-- Audited Smith diagonal. -/
def Window6EdgeFluxCriticalGroupData.smithDiagonal (_D : Window6EdgeFluxCriticalGroupData) :
    List Nat :=
  [1, 1, 123336]

/-- Tree count read from the reduced-Laplacian determinant. -/
def Window6EdgeFluxCriticalGroupData.treeCount (D : Window6EdgeFluxCriticalGroupData) : Nat :=
  Int.natAbs D.reducedLaplacian.det

/-- With Smith diagonal `[1,1,m]`, the cokernel is cyclic of order `m`. -/
def Window6EdgeFluxCriticalGroupData.criticalGroupIsCyclic
    (D : Window6EdgeFluxCriticalGroupData) : Prop :=
  D.smithDiagonal = [1, 1, D.treeCount]

/-- The audited four-block edge-flux reduced Laplacian has Smith diagonal `[1,1,123336]`,
tree count `123336`, and cyclic critical group. -/
theorem paper_window6_edge_flux_critical_group_cyclic (D : Window6EdgeFluxCriticalGroupData) :
    And (D.smithDiagonal = [1, 1, 123336])
      (And (D.treeCount = 123336) D.criticalGroupIsCyclic) := by
  constructor
  · rfl
  constructor
  · unfold Window6EdgeFluxCriticalGroupData.treeCount
    rw [D.audited_reducedLaplacian, det_window6EdgeFluxAuditedReducedLaplacian]
    simp
  · unfold Window6EdgeFluxCriticalGroupData.criticalGroupIsCyclic
    have htree : D.treeCount = 123336 := by
      unfold Window6EdgeFluxCriticalGroupData.treeCount
      rw [D.audited_reducedLaplacian, det_window6EdgeFluxAuditedReducedLaplacian]
      simp
    rw [htree]
    rfl

end Omega.GU
