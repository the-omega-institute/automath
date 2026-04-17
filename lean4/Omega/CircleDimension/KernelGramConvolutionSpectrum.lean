import Mathlib.Data.Real.Basic
import Omega.CircleDimension.KernelIntegerTranslateRieszBounds

namespace Omega.CircleDimension

/-- Closed interval cut out by the exact Gram-convolution symbol bounds. -/
noncomputable def kernelGramConvolutionSpectralInterval : Set ℝ :=
  Set.Icc Omega.CircleDimension.kernelIntegerTranslateLowerBound
    Omega.CircleDimension.kernelIntegerTranslateUpperBound

/-- The lower endpoint is attained at the Fourier boundary point `θ = π`. -/
def kernelGramConvolutionSharpLower : Prop :=
  Omega.CircleDimension.kernelIntegerTranslateSymbol Real.pi =
    Omega.CircleDimension.kernelIntegerTranslateLowerBound

/-- The upper endpoint is attained at the Fourier boundary point `θ = 0`. -/
def kernelGramConvolutionSharpUpper : Prop :=
  Omega.CircleDimension.kernelIntegerTranslateSymbol 0 =
    Omega.CircleDimension.kernelIntegerTranslateUpperBound

/-- Paper-facing Gram-convolution spectrum package: the closed-form symbol stays inside the sharp
spectral interval on `[-π, π]`, and the endpoints `π` and `0` realize the lower/upper edges.
    prop:cdim-kernel-gram-convolution-spectrum -/
theorem paper_cdim_kernel_gram_convolution_spectrum :
    (∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      Omega.CircleDimension.kernelIntegerTranslateSymbol θ ∈
        kernelGramConvolutionSpectralInterval) ∧
    kernelGramConvolutionSharpLower ∧ kernelGramConvolutionSharpUpper := by
  simpa [kernelGramConvolutionSpectralInterval, kernelGramConvolutionSharpLower,
    kernelGramConvolutionSharpUpper, Set.mem_Icc] using
    Omega.CircleDimension.paper_cdim_kernel_integer_translate_riesz_bounds

end Omega.CircleDimension
