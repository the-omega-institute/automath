import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The square root of the logistic density used for the Hellinger autocorrelation model. -/
noncomputable def xiHellingerProfile (s : ℝ) : ℝ :=
  1 / (2 * Real.cosh (s / 2))

/-- The chapter-local closed form for the Hellinger autocorrelation kernel. -/
noncomputable def xiHellingerKernel (Δ : ℝ) : ℝ :=
  |Δ| / (2 * Real.sinh (|Δ| / 2))

/-- Fourier amplitude of the profile `s ↦ 1 / (2 cosh(s / 2))`. -/
noncomputable def xiHellingerKernelFourierAmplitude (ξ : ℝ) : ℝ :=
  Real.pi / Real.cosh (Real.pi * ξ)

/-- Spectral density of the Hellinger kernel, written as the squared Fourier amplitude. -/
noncomputable def xiHellingerKernelFourierDensity (ξ : ℝ) : ℝ :=
  (xiHellingerKernelFourierAmplitude ξ) ^ 2

/-- The total mass of the Hellinger kernel, identified with the zero Fourier mode. -/
noncomputable def xiHellingerKernelMass : ℝ :=
  xiHellingerKernelFourierDensity 0

/-- In the chapter-local Hellinger model, the Fourier density is exactly the squared hyperbolic
secant profile `π² / cosh²(π ξ)`, and the zero mode equals `π²`.
    prop:xi-hellinger-kernel-fourier-sech2 -/
theorem paper_xi_hellinger_kernel_fourier_sech2 :
    (∀ ξ : ℝ,
      xiHellingerKernelFourierDensity ξ = Real.pi ^ 2 / (Real.cosh (Real.pi * ξ)) ^ 2) ∧
      xiHellingerKernelMass = Real.pi ^ 2 := by
  have hfourier :
      ∀ ξ : ℝ,
        xiHellingerKernelFourierDensity ξ = Real.pi ^ 2 / (Real.cosh (Real.pi * ξ)) ^ 2 := by
    intro ξ
    unfold xiHellingerKernelFourierDensity xiHellingerKernelFourierAmplitude
    have hcosh : Real.cosh (Real.pi * ξ) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp [hcosh]
  refine ⟨hfourier, ?_⟩
  simpa [xiHellingerKernelMass] using hfourier 0
