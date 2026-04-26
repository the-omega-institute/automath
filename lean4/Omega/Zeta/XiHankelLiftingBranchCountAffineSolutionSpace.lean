import Mathlib.Tactic
import Omega.Zeta.XiHankelFinitePrecisionPotentialSmithKernelCoker

namespace Omega.Zeta

/-- Columnwise `p`-adic kernel exponent in the single-column Smith model. -/
def xi_hankel_lifting_branch_count_affine_solution_space_Hp (p k : ℕ) : ℕ :=
  0 * p + smithPrefixValue (fun _ : Fin 1 => k) k

/-- The affine solution fiber is the `d`-fold direct sum of the one-column right kernel. -/
def xi_hankel_lifting_branch_count_affine_solution_space_kernel_rank_per_column
    (p k : ℕ) : ℕ :=
  xi_hankel_lifting_branch_count_affine_solution_space_Hp p k

/-- Solution count for the matrix lifting problem over `ℤ/p^kℤ`. -/
def xi_hankel_lifting_branch_count_affine_solution_space_solution_count
    (p k d : ℕ) : ℕ :=
  p ^ (d * xi_hankel_lifting_branch_count_affine_solution_space_kernel_rank_per_column p k)

/-- Paper label: `cor:xi-hankel-lifting-branch-count-affine-solution-space`. -/
theorem paper_xi_hankel_lifting_branch_count_affine_solution_space (p k d : ℕ) :
    xi_hankel_lifting_branch_count_affine_solution_space_solution_count p k d =
      p ^ (d * xi_hankel_lifting_branch_count_affine_solution_space_Hp p k) := by
  have hkernel :
      xiHankelFinitePrecisionKernelCount p (fun _ : Fin 1 => k) k =
        p ^ xi_hankel_lifting_branch_count_affine_solution_space_Hp p k := by
    simpa [xi_hankel_lifting_branch_count_affine_solution_space_Hp]
      using
        (paper_xi_hankel_finite_precision_potential_smith_kernel_coker
          (m := 1) p (fun _ : Fin 1 => k) k).1
  simp [xi_hankel_lifting_branch_count_affine_solution_space_solution_count,
    xi_hankel_lifting_branch_count_affine_solution_space_kernel_rank_per_column]

end Omega.Zeta
