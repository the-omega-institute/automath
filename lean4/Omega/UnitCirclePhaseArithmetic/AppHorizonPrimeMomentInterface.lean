import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppHorizonCoeffLocal

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The absolutely convergent Euler-patch radius used by the appendix horizon expansion. -/
def app_horizon_prime_moment_interface_patch_radius : ℝ :=
  1 / 3

/-- The local Cayley-side coordinate remains in the audited patch. -/
def app_horizon_prime_moment_interface_in_patch (w : ℝ) : Prop :=
  |w| < app_horizon_prime_moment_interface_patch_radius

/-- The appendix horizon change of variables with center `σ(0) = 3 / 2`. -/
def app_horizon_prime_moment_interface_sigma (w : ℝ) : ℝ :=
  (3 - w) / (2 * (1 + w))

/-- The convergent prime-moment sum audited at `s = 3 / 2`. -/
def app_horizon_prime_moment_interface_prime_moment_sum (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  M k

/-- The constant Taylor coefficient extracted from the local jet. -/
def app_horizon_prime_moment_interface_coeff0 (M : ℕ → ℝ) : ℝ :=
  appHorizonCoeffC0 (app_horizon_prime_moment_interface_prime_moment_sum M 0)

/-- The linear Taylor coefficient extracted from the local jet. -/
def app_horizon_prime_moment_interface_coeff1 (M : ℕ → ℝ) : ℝ :=
  appHorizonCoeffC1 (app_horizon_prime_moment_interface_prime_moment_sum M 1)

/-- The quadratic Taylor coefficient extracted from the local jet. -/
def app_horizon_prime_moment_interface_coeff2 (M : ℕ → ℝ) : ℝ :=
  appHorizonCoeffC2
    (app_horizon_prime_moment_interface_prime_moment_sum M 1)
    (app_horizon_prime_moment_interface_prime_moment_sum M 2)

/-- The cubic Taylor coefficient extracted from the local jet. -/
def app_horizon_prime_moment_interface_coeff3 (M : ℕ → ℝ) : ℝ :=
  appHorizonCoeffC3
    (app_horizon_prime_moment_interface_prime_moment_sum M 1)
    (app_horizon_prime_moment_interface_prime_moment_sum M 2)
    (app_horizon_prime_moment_interface_prime_moment_sum M 3)

lemma app_horizon_prime_moment_interface_origin_in_patch :
    app_horizon_prime_moment_interface_in_patch 0 := by
  norm_num [app_horizon_prime_moment_interface_in_patch,
    app_horizon_prime_moment_interface_patch_radius]

lemma app_horizon_prime_moment_interface_sigma_at_zero :
    app_horizon_prime_moment_interface_sigma 0 = 3 / 2 := by
  norm_num [app_horizon_prime_moment_interface_sigma]

/-- Paper label: `cor:app-horizon-prime-moment-interface`. Inside the audited Euler patch
`|w| < 1 / 3`, the center `w = 0` corresponds to `σ = 3 / 2`, and the first four Taylor
coefficients are explicit finite rational combinations of the prime-moment sums `M₀, …, M₃`. -/
theorem paper_app_horizon_prime_moment_interface (M : ℕ → ℝ) :
    app_horizon_prime_moment_interface_in_patch 0 ∧
    app_horizon_prime_moment_interface_sigma 0 = 3 / 2 ∧
    app_horizon_prime_moment_interface_coeff0 M =
      -app_horizon_prime_moment_interface_prime_moment_sum M 0 ∧
    app_horizon_prime_moment_interface_coeff1 M =
      -app_horizon_prime_moment_interface_prime_moment_sum M 1 ∧
    app_horizon_prime_moment_interface_coeff2 M =
      app_horizon_prime_moment_interface_prime_moment_sum M 1 -
        app_horizon_prime_moment_interface_prime_moment_sum M 2 ∧
    app_horizon_prime_moment_interface_coeff3 M =
      -app_horizon_prime_moment_interface_prime_moment_sum M 1 +
        2 * app_horizon_prime_moment_interface_prime_moment_sum M 2 -
          ((2 : ℝ) / 3) * app_horizon_prime_moment_interface_prime_moment_sum M 3 := by
  refine ⟨app_horizon_prime_moment_interface_origin_in_patch,
    app_horizon_prime_moment_interface_sigma_at_zero, ?_⟩
  simpa [app_horizon_prime_moment_interface_coeff0, app_horizon_prime_moment_interface_coeff1,
    app_horizon_prime_moment_interface_coeff2, app_horizon_prime_moment_interface_coeff3,
    app_horizon_prime_moment_interface_prime_moment_sum] using
    paper_app_horizon_coeff_local (M 0) (M 1) (M 2) (M 3)

end

end Omega.UnitCirclePhaseArithmetic
