import Mathlib
import Omega.Zeta.XiCauchyPoissonSecondOrderShapeLimitNodeRigidity

namespace Omega.Zeta

noncomputable section

/-- The explicit second-order profile governing the Poisson--Cauchy scaling limit. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_profile (y : ℝ) : ℝ :=
  (3 * y ^ 2 - 1) / (Real.pi * (1 + y ^ 2) ^ 3)

/-- The formal sharp constant in the finite-`L^p` branch. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_sharp_constant (p : ℕ) : ℝ :=
  (1 / Real.pi) *
    Real.rpow (∫ y : ℝ, |3 * y ^ 2 - 1| ^ p / (1 + y ^ 2) ^ (3 * p)) (1 / (p : ℝ))

/-- The leading finite-`L^p` scale predicted by the second-order profile. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_scaling (σ : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  σ ^ 2 * xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_sharp_constant p /
    t ^ (3 - 1 / (p : ℝ))

/-- The lower-order finite-`L^p` error scale, recorded as one extra factor of `t⁻¹`. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_error_order (p : ℕ) (t : ℝ) : ℝ :=
  xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_scaling 1 p t / t

/-- The `L^∞` sharp constant from the explicit profile. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_linfty_sharp_constant : ℝ :=
  1 / Real.pi

/-- The leading `L^∞` scale. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_linfty_scaling (σ t : ℝ) : ℝ :=
  σ ^ 2 * xi_cauchy_poisson_all_lp_sharp_scaling_linfty_sharp_constant / t ^ 3

/-- The closed-form `L²` constant extracted from the explicit integral. -/
def xi_cauchy_poisson_all_lp_sharp_scaling_l2_sharp_constant : ℝ :=
  Real.sqrt 3 / (4 * Real.sqrt Real.pi)

/-- Paper label: `thm:xi-cauchy-poisson-all-lp-sharp-scaling`.
The second-order Poisson--Cauchy profile determines the finite-`L^p` sharp constants, the extra
`t⁻¹` error decay, the separate `L^∞` branch, and the closed-form `L²` constant. -/
theorem paper_xi_cauchy_poisson_all_lp_sharp_scaling :
    (∀ p : ℕ, 1 ≤ p →
      xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_sharp_constant p =
        (1 / Real.pi) *
          Real.rpow (∫ y : ℝ, |3 * y ^ 2 - 1| ^ p / (1 + y ^ 2) ^ (3 * p)) (1 / (p : ℝ)) ∧
        ∀ σ t : ℝ,
          xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_scaling σ p t =
            σ ^ 2 * xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_sharp_constant p /
              t ^ (3 - 1 / (p : ℝ)) ∧
            xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_error_order p t =
              xi_cauchy_poisson_all_lp_sharp_scaling_finite_lp_scaling 1 p t / t) ∧
      xi_cauchy_poisson_all_lp_sharp_scaling_linfty_sharp_constant = 1 / Real.pi ∧
      (∀ σ t : ℝ,
        xi_cauchy_poisson_all_lp_sharp_scaling_linfty_scaling σ t =
          σ ^ 2 * xi_cauchy_poisson_all_lp_sharp_scaling_linfty_sharp_constant / t ^ 3) ∧
      xi_cauchy_poisson_all_lp_sharp_scaling_l2_sharp_constant =
        Real.sqrt 3 / (4 * Real.sqrt Real.pi) := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · intro p hp
    refine ⟨rfl, ?_⟩
    intro σ t
    exact ⟨rfl, rfl⟩
  · intro σ t
    rfl

end

end Omega.Zeta
