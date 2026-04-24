import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The one-variable `H_m` kernel determined by the fiber multiplicity data `d`. -/
def xiHmKernel {α : Type} [Fintype α] (d : α → ℚ) (z : ℚ) : ℚ :=
  ∏ x, (1 - d x * z)⁻¹

/-- The Schur generating series after the Schur-trace identification, written as a product over
fiber multiplicities first and auxiliary variables second. -/
def xiSchurTraceSeries {α β : Type} [Fintype α] [Fintype β] (d : α → ℚ) (y : β → ℚ) : ℚ :=
  ∏ x, ∏ j, (1 - d x * y j)⁻¹

/-- The Cauchy master kernel obtained by externalizing through the auxiliary variables. -/
def xiSchurCauchyMasterKernel {α β : Type} [Fintype α] [Fintype β] (d : α → ℚ) (y : β → ℚ) : ℚ :=
  ∏ j, ∏ x, (1 - d x * y j)⁻¹

/-- The Schur master kernel can be written either as the finite Cauchy product over all fiber
multiplicities and auxiliary variables or as the externalized product of the one-variable kernels
`H_m(y_j)`.
    thm:xi-time-part63c-schur-cauchy-master-kernel -/
theorem paper_xi_time_part63c_schur_cauchy_master_kernel :
    ∀ {α β : Type} [Fintype α] [Fintype β] (d : α → ℚ) (y : β → ℚ),
      xiSchurTraceSeries d y = xiSchurCauchyMasterKernel d y ∧
        xiSchurCauchyMasterKernel d y = ∏ j, xiHmKernel d (y j) := by
  intro α β _ _ d y
  refine ⟨?_, ?_⟩
  · rw [xiSchurTraceSeries, xiSchurCauchyMasterKernel]
    exact Finset.prod_comm
  · simp [xiSchurCauchyMasterKernel, xiHmKernel]

end Omega.Zeta
