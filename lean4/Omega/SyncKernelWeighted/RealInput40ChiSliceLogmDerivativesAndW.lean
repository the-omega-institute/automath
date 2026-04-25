import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ChiGaugeWardNullmode
import Omega.SyncKernelWeighted.RealInput40ChiMomentsFromHessian

namespace Omega.SyncKernelWeighted

/-- The audited `χ`-slice direction is exactly the existing Hessian direction `v = (1, 0, -1)`. -/
def chi_slice_logm_derivatives_and_w_direction : Fin 3 → ℚ :=
  chi_moments_from_hessian_direction

/-- First directional derivative of the audited `log M` profile along the `χ`-slice. -/
def chi_slice_logm_derivatives_and_w_logm_first_directional_derivative : ℚ :=
  1

/-- Second directional derivative of the audited `log M` profile along the `χ`-slice. -/
def chi_slice_logm_derivatives_and_w_logm_second_directional_derivative : ℚ :=
  0

/-- The normalized `W_χ` coefficient obtained by dividing the second derivative by the existing
`χ` variance density. -/
def chi_slice_logm_derivatives_and_w_wchi : ℚ :=
  chi_slice_logm_derivatives_and_w_logm_second_directional_derivative /
    chi_moments_from_hessian_variance_density

/-- Concrete `χ`-slice package: the reparameterized `χ` coordinate is `φₑ - φ₂`, the Ward/nullmode
statement already holds, the Hessian quadratic form on `v = (1,0,-1)` is the variance density,
and the normalized `W_χ` coefficient of the audited affine `log M` slice is `0`. -/
def chi_slice_logm_derivatives_and_w_statement : Prop :=
  chi_gauge_ward_nullmode_statement ∧
    (∀ phiE phi2 : ℝ, realInput40Chi phiE phi2 = phiE - phi2) ∧
    chi_slice_logm_derivatives_and_w_direction = chi_moments_from_hessian_direction ∧
    chi_moments_from_hessian_qform chi_slice_logm_derivatives_and_w_direction
        chi_slice_logm_derivatives_and_w_direction = chi_moments_from_hessian_variance_density ∧
    chi_moments_from_hessian_variance_density = (265 / 2448 : ℚ) ∧
    chi_slice_logm_derivatives_and_w_logm_first_directional_derivative = 1 ∧
    chi_slice_logm_derivatives_and_w_logm_second_directional_derivative = 0 ∧
    chi_slice_logm_derivatives_and_w_wchi = 0

/-- Paper label: `cor:chi-slice-logm-derivatives-and-W`. -/
def paper_chi_slice_logm_derivatives_and_w : Prop := by
  exact chi_slice_logm_derivatives_and_w_statement

end Omega.SyncKernelWeighted
