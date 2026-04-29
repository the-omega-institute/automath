import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Matrix

/-- The audited three-potential Hessian at the origin. -/
def syncKernel3DHessianMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(11 : ℚ) / 102, 0, 181 / 1632;
    0, 25 / 128, 5 / 128;
    181 / 1632, 5 / 128, 2 / 9]

/-- The exact rational inverse of the audited three-potential Hessian. -/
def syncKernel3DHessianInverseMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1713192 : ℚ) / 86473, 886176 / 432365, -(886176 / 86473);
    886176 / 432365, 2386048 / 432365, -(861696 / 432365);
    -(886176 / 86473), -(861696 / 432365), 861696 / 86473]

/-- Paper label: `prop:sync-kernel-3d-hessian-inverse-exact`. -/
theorem paper_sync_kernel_3d_hessian_inverse_exact :
    syncKernel3DHessianMatrix * syncKernel3DHessianInverseMatrix = 1 ∧
      syncKernel3DHessianInverseMatrix * syncKernel3DHessianMatrix = 1 := by
  native_decide

end Omega.SyncKernelWeighted
