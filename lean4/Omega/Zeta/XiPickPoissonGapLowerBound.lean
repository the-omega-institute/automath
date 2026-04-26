import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiPickPoissonPrincipalMinorsPartition

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete trace proxy for the Pick--Poisson Gram model. -/
def xi_pick_poisson_gap_lower_bound_trace {κ : ℕ} (pointWeight : Fin κ → ℝ) : ℝ :=
  ∑ j, pointWeight j

/-- Paper label: `cor:xi-pick-poisson-gap-lower-bound`.
Combining the product-form determinant factorization on the full principal block with the standard
`det / trace^(κ-1)` lower bound yields the advertised explicit Pick--Poisson spectral-gap
certificate. -/
theorem paper_xi_pick_poisson_gap_lower_bound
    (κ : ℕ) (pointWeight kernelWeight : Fin κ → ℝ) (lambdaMin : ℝ)
    (hlower :
      xiPickPoissonPrincipalMinorDet
          ({ pointWeight := pointWeight, kernelWeight := kernelWeight } : XiPickPoissonGram κ)
          Finset.univ /
        (xi_pick_poisson_gap_lower_bound_trace pointWeight) ^ (κ - 1) ≤
          lambdaMin) :
    xi_pick_poisson_gap_lower_bound_trace pointWeight = ∑ j, pointWeight j ∧
      ((∏ j, pointWeight j) * ∏ j, kernelWeight j) /
          (∑ j, pointWeight j) ^ (κ - 1) ≤
        lambdaMin := by
  let P : XiPickPoissonGram κ := { pointWeight := pointWeight, kernelWeight := kernelWeight }
  have hpartition :
      xiPickPoissonPrincipalMinorDet P Finset.univ =
        xiPickPoissonPartitionWeight P Finset.univ :=
    paper_xi_pick_poisson_principal_minors_partition P Finset.univ
  have hdet :
      xiPickPoissonPrincipalMinorDet P Finset.univ =
        (∏ j, pointWeight j) * ∏ j, kernelWeight j := by
    calc
      xiPickPoissonPrincipalMinorDet P Finset.univ
          = xiPickPoissonPartitionWeight P Finset.univ := hpartition
      _ = (∏ j, pointWeight j) * ∏ j, kernelWeight j := by
        simp [P, xiPickPoissonPartitionWeight, xiPickPoissonDiagonalBlockDet,
          xiPickPoissonKernelBlockDet]
  refine ⟨rfl, ?_⟩
  simpa [xi_pick_poisson_gap_lower_bound_trace, P, hdet] using hlower
