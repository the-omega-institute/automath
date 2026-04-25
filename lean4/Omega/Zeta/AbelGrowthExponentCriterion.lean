import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Cauchy-Hadamard radius encoded by the growth exponent `κ`. -/
def abel_growth_exponent_criterion_cauchy_radius (κ : ℝ) : ℝ :=
  Real.exp (-κ)

/-- Radius encoded by the rightmost real part `σ`. -/
def abel_growth_exponent_criterion_sigma_radius (b σ : ℝ) : ℝ :=
  Real.exp (-(σ - 1 / 2) * Real.log b)

/-- A concrete logarithmic rearrangement of the radius identity. -/
theorem paper_abel_growth_exponent_criterion (b σ κ : ℝ) (hb : 1 < b)
    (hrad :
      abel_growth_exponent_criterion_cauchy_radius κ =
        abel_growth_exponent_criterion_sigma_radius b σ) :
    σ = 1 / 2 + κ / Real.log b ∧ (σ = 1 / 2 ↔ κ = 0) := by
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hlog_eq : -κ = -(σ - 1 / 2) * Real.log b := by
    apply_fun Real.log at hrad
    simpa [abel_growth_exponent_criterion_cauchy_radius,
      abel_growth_exponent_criterion_sigma_radius] using hrad
  have hκ : κ = (σ - 1 / 2) * Real.log b := by
    linarith
  have hlogb : Real.log b ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one hbpos (ne_of_gt hb)
  have hσ : σ = 1 / 2 + κ / Real.log b := by
    have hdiv : κ / Real.log b = σ - 1 / 2 := by
      apply (div_eq_iff hlogb).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hκ
    linarith
  refine ⟨hσ, ?_⟩
  constructor
  · intro hσhalf
    rw [hσhalf] at hκ
    simpa using hκ
  · intro hκzero
    simpa [hκzero] using hσ

end

end Omega.Zeta
