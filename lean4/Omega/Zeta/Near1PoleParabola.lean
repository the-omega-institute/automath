import Omega.Zeta.Near1PoleDiffusiveSp

namespace Omega.Zeta

/-- Concrete near-`1` pole data after the diffusive small-angle expansion has identified the
linear imaginary drift and quadratic real dissipation coefficients. -/
structure near1_pole_parabola_data where
  logLam : ℝ
  mu2 : ℝ
  sigma2Sq : ℝ
  scale : ℕ → ℝ
  realDefect : ℕ → ℝ
  imagPart : ℕ → ℝ
  logLam_ne_zero : logLam ≠ 0
  mu2_ne_zero : mu2 ≠ 0
  real_expansion :
    ∀ m : ℕ, realDefect m = (sigma2Sq / (2 * logLam)) * scale m ^ 2
  imag_expansion :
    ∀ m : ℕ, imagPart m = (mu2 / logLam) * scale m

/-- The parabolic coefficient obtained after eliminating the scale parameter. -/
noncomputable def near1_pole_parabola_coefficient (D : near1_pole_parabola_data) : ℝ :=
  D.sigma2Sq * D.logLam / (2 * D.mu2 ^ 2)

/-- The paper-facing parabolic relation between real defect and squared imaginary displacement. -/
def near1_pole_parabola_statement (D : near1_pole_parabola_data) : Prop :=
  ∀ m : ℕ,
    D.realDefect m = near1_pole_parabola_coefficient D * D.imagPart m ^ 2

/-- Paper label: `cor:near1-pole-parabola`. -/
theorem paper_near1_pole_parabola (D : near1_pole_parabola_data) :
    near1_pole_parabola_statement D := by
  intro m
  rw [D.real_expansion m, D.imag_expansion m, near1_pole_parabola_coefficient]
  field_simp [D.logLam_ne_zero, D.mu2_ne_zero]

end Omega.Zeta
