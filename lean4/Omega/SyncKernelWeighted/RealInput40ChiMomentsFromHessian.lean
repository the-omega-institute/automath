import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ChiReparam4d
import Omega.SyncKernelWeighted.SyncKernel3DHessianInverseExact

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- The `χ`-slice direction `v = (1, 0, -1)`. -/
def chi_moments_from_hessian_direction : Fin 3 → ℚ :=
  ![(1 : ℚ), 0, -1]

/-- The `φ₋` axis in the three-potential pressure coordinates. -/
def chi_moments_from_hessian_phi_minus_axis : Fin 3 → ℚ :=
  ![0, (1 : ℚ), 0]

/-- The Hessian quadratic form evaluated on two coordinate vectors. -/
def chi_moments_from_hessian_qform (x y : Fin 3 → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * syncKernel3DHessianMatrix i j * y j

/-- The audited `χ` mean density on the `v = (1, 0, -1)` slice. -/
noncomputable def chi_moments_from_hessian_mean_density : ℝ :=
  (17 - 5 * Real.sqrt 5) / 20

/-- The `χ` variance density read off from the Hessian entry combination
`∂²_{θₑθₑ} + ∂²_{θ₂θ₂} - 2 ∂²_{θₑθ₂}`. -/
def chi_moments_from_hessian_variance_density : ℚ :=
  syncKernel3DHessianMatrix 0 0 + syncKernel3DHessianMatrix 2 2 -
    2 * syncKernel3DHessianMatrix 0 2

/-- The `χ/φ₋` covariance density read off from the Hessian entry combination
`∂²_{θₑθ₋} - ∂²_{θ₂θ₋}`. -/
def chi_moments_from_hessian_covariance_density : ℚ :=
  syncKernel3DHessianMatrix 0 1 - syncKernel3DHessianMatrix 2 1

lemma chi_moments_from_hessian_direction_variance :
    chi_moments_from_hessian_qform chi_moments_from_hessian_direction
        chi_moments_from_hessian_direction = chi_moments_from_hessian_variance_density := by
  native_decide

lemma chi_moments_from_hessian_direction_covariance :
    chi_moments_from_hessian_qform chi_moments_from_hessian_direction
        chi_moments_from_hessian_phi_minus_axis = chi_moments_from_hessian_covariance_density := by
  native_decide

lemma chi_moments_from_hessian_variance_density_eq :
    chi_moments_from_hessian_variance_density = (265 / 2448 : ℚ) := by
  native_decide

lemma chi_moments_from_hessian_covariance_density_eq :
    chi_moments_from_hessian_covariance_density = (-(5 / 128 : ℚ)) := by
  native_decide

/-- Paper label: `cor:chi-moments-from-hessian`. On the `χ`-slice `v = (1, 0, -1)` the observable
is exactly the reparameterized difference `φₑ - φ₂`, the mean density is the audited closed form,
and the variance/covariance are the corresponding Hessian linear combinations. -/
theorem paper_chi_moments_from_hessian :
    (∀ phiE phi2 : ℝ, realInput40Chi phiE phi2 = phiE - phi2) ∧
      chi_moments_from_hessian_mean_density = (17 - 5 * Real.sqrt 5) / 20 ∧
      chi_moments_from_hessian_variance_density =
        syncKernel3DHessianMatrix 0 0 + syncKernel3DHessianMatrix 2 2 -
          2 * syncKernel3DHessianMatrix 0 2 ∧
      chi_moments_from_hessian_covariance_density =
        syncKernel3DHessianMatrix 0 1 - syncKernel3DHessianMatrix 2 1 ∧
      chi_moments_from_hessian_qform chi_moments_from_hessian_direction
          chi_moments_from_hessian_direction = chi_moments_from_hessian_variance_density ∧
      chi_moments_from_hessian_qform chi_moments_from_hessian_direction
          chi_moments_from_hessian_phi_minus_axis = chi_moments_from_hessian_covariance_density ∧
      chi_moments_from_hessian_variance_density = (265 / 2448 : ℚ) ∧
      chi_moments_from_hessian_covariance_density = (-(5 / 128 : ℚ)) := by
  refine ⟨?_, rfl, rfl, rfl, chi_moments_from_hessian_direction_variance,
    chi_moments_from_hessian_direction_covariance, ?_, ?_⟩
  · intro phiE phi2
    rfl
  · exact chi_moments_from_hessian_variance_density_eq
  · exact chi_moments_from_hessian_covariance_density_eq

end Omega.SyncKernelWeighted
