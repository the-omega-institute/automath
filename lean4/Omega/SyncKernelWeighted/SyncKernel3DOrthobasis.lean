import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SyncKernel3DHessianInverseExact

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- The `η` combination from the audited exact Gram--Schmidt step. -/
def sync_kernel_3d_orthobasis_eta : Fin 3 → ℚ :=
  ![(1 : ℚ), 0, -(543 / 1088 : ℚ)]

/-- The intermediate `ψ` combination before the final orthogonal correction. -/
def sync_kernel_3d_orthobasis_psi : Fin 3 → ℚ :=
  ![0, (1 : ℚ), -(45 / 256 : ℚ)]

/-- The corrected `ψ'` vector from the audited exact Gram--Schmidt step. -/
def sync_kernel_3d_orthobasis_psiprime : Fin 3 → ℚ :=
  sync_kernel_3d_orthobasis_psi + (27693 / 74564 : ℚ) • sync_kernel_3d_orthobasis_eta

/-- The original third basis vector `φ₂`. -/
def sync_kernel_3d_orthobasis_phi2 : Fin 3 → ℚ :=
  ![0, 0, (1 : ℚ)]

/-- The Hessian Gram form at the audited critical point. -/
def sync_kernel_3d_orthobasis_qform (x y : Fin 3 → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * syncKernel3DHessianMatrix i j * y j

/-- Paper label: `cor:sync-kernel-3d-orthobasis`. -/
theorem paper_sync_kernel_3d_orthobasis :
    sync_kernel_3d_orthobasis_qform
        sync_kernel_3d_orthobasis_eta
        sync_kernel_3d_orthobasis_psiprime = 0 ∧
      sync_kernel_3d_orthobasis_qform
        sync_kernel_3d_orthobasis_eta
        sync_kernel_3d_orthobasis_phi2 = 0 ∧
      sync_kernel_3d_orthobasis_qform
        sync_kernel_3d_orthobasis_psiprime
        sync_kernel_3d_orthobasis_phi2 = 0 ∧
      sync_kernel_3d_orthobasis_qform
        sync_kernel_3d_orthobasis_eta
        sync_kernel_3d_orthobasis_eta = 93205 / 1775616 ∧
      sync_kernel_3d_orthobasis_qform
        sync_kernel_3d_orthobasis_psiprime
        sync_kernel_3d_orthobasis_psiprime = 432365 / 2386048 ∧
      sync_kernel_3d_orthobasis_qform
        sync_kernel_3d_orthobasis_phi2
        sync_kernel_3d_orthobasis_phi2 = 2 / 9 := by
  native_decide

end Omega.SyncKernelWeighted
