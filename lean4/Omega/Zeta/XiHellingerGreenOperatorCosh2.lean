import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Zeta.XiHellingerKernelFourierSech2

namespace Omega.Zeta

/-- The Fourier multiplier corresponding to the chapter-local `cosh²` Green operator. -/
noncomputable def xi_hellinger_green_operator_cosh2_multiplier (ξ : ℝ) : ℝ :=
  (Real.cosh (Real.pi * ξ)) ^ 2 / Real.pi ^ 2

/-- Applying the `cosh²` Green operator to the Hellinger kernel density multiplies by the explicit
reciprocal Fourier factor. -/
noncomputable def xi_hellinger_green_operator_cosh2_density (ξ : ℝ) : ℝ :=
  xi_hellinger_green_operator_cosh2_multiplier ξ * xiHellingerKernelFourierDensity ξ

/-- Paper label: `prop:xi-hellinger-green-operator-cosh2`. The Hellinger kernel Fourier density is
`π² / cosh²(π ξ)`, so the `cosh²` Green operator cancels it pointwise and leaves the constant
kernel `1`. -/
theorem paper_xi_hellinger_green_operator_cosh2 :
    (∀ ξ : ℝ,
      xiHellingerKernelFourierDensity ξ = Real.pi ^ 2 / (Real.cosh (Real.pi * ξ)) ^ 2) ∧
      (∀ ξ : ℝ, xi_hellinger_green_operator_cosh2_density ξ = 1) := by
  rcases paper_xi_hellinger_kernel_fourier_sech2 with ⟨hfourier, _⟩
  refine ⟨hfourier, ?_⟩
  intro ξ
  rw [xi_hellinger_green_operator_cosh2_density, xi_hellinger_green_operator_cosh2_multiplier,
    hfourier ξ]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hcosh : Real.cosh (Real.pi * ξ) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp [hpi, hcosh]

end Omega.Zeta
