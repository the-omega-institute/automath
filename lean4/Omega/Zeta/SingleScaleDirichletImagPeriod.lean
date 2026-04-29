import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The single-scale Dirichletized function attached to `g` and the base `L`. -/
def single_scale_dirichlet_imag_period_dirichletized {α : Type*} (g : ℂ → α) (L : ℝ) (s : ℂ) : α :=
  g (Complex.exp (-s * (Real.log L : ℂ)))

/-- Paper label: `prop:single-scale-dirichlet-imag-period`. Shifting the imaginary part of `s` by
`2π / log L` multiplies the exponent by `exp (-2π i) = 1`, so the single-scale Dirichletized
function is exactly periodic in the imaginary direction. -/
theorem paper_single_scale_dirichlet_imag_period {α : Type*} (g : ℂ → α) {L : ℝ} (hL : 1 < L)
    (s : ℂ) :
    single_scale_dirichlet_imag_period_dirichletized g L
        (s + (2 * Real.pi * Complex.I) / (Real.log L : ℂ)) =
      single_scale_dirichlet_imag_period_dirichletized g L s := by
  have hlogL : (Real.log L : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hL).ne'
  have hsplit :
      -(s + (2 * Real.pi * Complex.I) / (Real.log L : ℂ)) * (Real.log L : ℂ) =
        (-s * (Real.log L : ℂ)) + (-(2 * Real.pi * Complex.I)) := by
    field_simp [hlogL]
    ring
  have hTexp : Complex.exp (-(2 * Real.pi * Complex.I)) = 1 := by
    simpa using Complex.exp_int_mul_two_pi_mul_I (-1)
  unfold single_scale_dirichlet_imag_period_dirichletized
  rw [hsplit, Complex.exp_add, hTexp, mul_one]

end

end Omega.Zeta
