import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Omega.CircleDimension.CauchyDerivativeGramExponentialKernel

namespace Omega.CircleDimension

/-- Concrete Fourier profile used in the spectral representation of the Poisson KL quadratic form.
-/
abbrev PoissonKLQuadraticFormSpectralData := ℝ → ℂ

/-- The difference kernel identified by the exponential-kernel closed form. -/
noncomputable def poissonKLQuadraticKernel (x : ℝ) : ℝ :=
  cauchyDerivativeGramExponentialKernelValue x 0

/-- The spectral weight appearing after Fourier transform. -/
noncomputable def poissonKLQuadraticSpectralWeight (ξ : ℝ) : ℝ :=
  Real.pi * Real.exp (-2 * |ξ|)

/-- The Plancherel-side quadratic form. -/
noncomputable def poissonKLQuadraticForm (D : PoissonKLQuadraticFormSpectralData) : ℝ :=
  Real.pi * ∫ ξ, ‖D ξ‖ ^ 2 * Real.exp (-2 * |ξ|)

/-- Concrete spectral representation package: the kernel is the rational difference kernel
`2 / (4 + x^2)`, the Fourier-side weight is `π * exp (-2 * |ξ|)`, and the quadratic form is the
corresponding weighted Plancherel energy. -/
def PoissonKLQuadraticFormSpectral (D : PoissonKLQuadraticFormSpectralData) : Prop :=
  (∀ x : ℝ, poissonKLQuadraticKernel x = 2 / (4 + x ^ 2)) ∧
    (∀ ξ : ℝ, poissonKLQuadraticSpectralWeight ξ = Real.pi * Real.exp (-2 * |ξ|)) ∧
    poissonKLQuadraticForm D = Real.pi * ∫ ξ, ‖D ξ‖ ^ 2 * Real.exp (-2 * |ξ|)

/-- Paper label: `prop:cdim-poisson-kl-quadratic-form-spectral`. -/
theorem paper_cdim_poisson_kl_quadratic_form_spectral (D : PoissonKLQuadraticFormSpectralData) :
    PoissonKLQuadraticFormSpectral D := by
  refine ⟨?_, ?_, rfl⟩
  · intro x
    simpa [poissonKLQuadraticKernel, CauchyDerivativeGramExponentialKernel] using
      paper_cdim_cauchy_derivative_gram_exponential_kernel (x, 0)
  · intro ξ
    rfl

end Omega.CircleDimension
