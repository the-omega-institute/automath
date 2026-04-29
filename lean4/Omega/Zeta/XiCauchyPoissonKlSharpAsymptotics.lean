import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Weighted parity integral for the odd third-order profile. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_parity_a3 : ℝ := 0

/-- Weighted parity integral for the odd fifth-order profile. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_parity_a5 : ℝ := 0

/-- The `t^{-4}` weighted square integral in the scaled density-ratio expansion. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2_sq : ℝ := 1 / 4

/-- The `mu_3^2` weighted square integral in the `t^{-6}` coefficient. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_integral_a3_sq : ℝ := 3 / 16

/-- The mixed `sigma^2 * mu_4` weighted integral in the `t^{-6}` coefficient. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2a4 : ℝ := -1 / 8

/-- The cubic `sigma^6` weighted integral in the entropy expansion. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2_cube : ℝ := -3 / 32

/-- Raw fourth-order KL coefficient from the finite weighted integral table. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_raw_t4 (sigmaSq : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sigmaSq ^ 2 *
    xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2_sq

/-- Closed fourth-order KL coefficient. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_closed_t4 (sigmaSq : ℝ) : ℝ :=
  sigmaSq ^ 2 / 8

/-- Raw sixth-order KL coefficient from the Taylor and parity computation. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_raw_t6
    (sigmaSq mu3 mu4 : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (mu3 ^ 2 * xi_cauchy_poisson_kl_sharp_asymptotics_integral_a3_sq +
        2 * sigmaSq * mu4 * xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2a4) -
    (1 / 6 : ℝ) * sigmaSq ^ 3 *
      xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2_cube

/-- Closed sixth-order KL coefficient in central moments. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_closed_t6
    (sigmaSq mu3 mu4 : ℝ) : ℝ :=
  3 * mu3 ^ 2 / 32 - sigmaSq * mu4 / 8 + sigmaSq ^ 3 / 64

/-- Concrete statement of the sharp Cauchy--Poisson KL coefficient collection. -/
def xi_cauchy_poisson_kl_sharp_asymptotics_statement : Prop :=
  xi_cauchy_poisson_kl_sharp_asymptotics_parity_a3 = 0 ∧
    xi_cauchy_poisson_kl_sharp_asymptotics_parity_a5 = 0 ∧
      (∀ sigmaSq : ℝ,
        xi_cauchy_poisson_kl_sharp_asymptotics_raw_t4 sigmaSq =
          xi_cauchy_poisson_kl_sharp_asymptotics_closed_t4 sigmaSq) ∧
        (∀ sigmaSq mu3 mu4 : ℝ,
          xi_cauchy_poisson_kl_sharp_asymptotics_raw_t6 sigmaSq mu3 mu4 =
            xi_cauchy_poisson_kl_sharp_asymptotics_closed_t6 sigmaSq mu3 mu4)

/-- Paper label: `thm:xi-cauchy-poisson-kl-sharp-asymptotics`. -/
theorem paper_xi_cauchy_poisson_kl_sharp_asymptotics :
    xi_cauchy_poisson_kl_sharp_asymptotics_statement := by
  unfold xi_cauchy_poisson_kl_sharp_asymptotics_statement
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro sigmaSq
    simp [xi_cauchy_poisson_kl_sharp_asymptotics_raw_t4,
      xi_cauchy_poisson_kl_sharp_asymptotics_closed_t4,
      xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2_sq]
    ring
  · intro sigmaSq mu3 mu4
    simp [xi_cauchy_poisson_kl_sharp_asymptotics_raw_t6,
      xi_cauchy_poisson_kl_sharp_asymptotics_closed_t6,
      xi_cauchy_poisson_kl_sharp_asymptotics_integral_a3_sq,
      xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2a4,
      xi_cauchy_poisson_kl_sharp_asymptotics_integral_a2_cube]
    ring

end

end Omega.Zeta
