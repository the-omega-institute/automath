import Mathlib.Tactic
import Omega.CircleDimension.KernelIntegerSamplingDualKernel

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for lattice sampling on the integer secant orbit.
    thm:poisson-lattice-sampling -/
theorem paper_circle_dimension_poisson_lattice_sampling
    (kernelRiesz secantRiesz kernelSynthesis secantSynthesis
      restrictionIsomorphism uniqueInterpolant : Prop)
    (hKernel : kernelRiesz)
    (hSecant : secantRiesz)
    (hKernelSynth : kernelRiesz → kernelSynthesis)
    (hSecantSynth : secantRiesz → secantSynthesis)
    (hRestrict : kernelSynthesis → restrictionIsomorphism)
    (hUnique : restrictionIsomorphism → uniqueInterpolant) :
    kernelRiesz ∧
      secantRiesz ∧
      kernelSynthesis ∧
      secantSynthesis ∧
      restrictionIsomorphism ∧
      uniqueInterpolant := by
  have hKernelSynthesis : kernelSynthesis := hKernelSynth hKernel
  have hSecantSynthesis : secantSynthesis := hSecantSynth hSecant
  have hRestriction : restrictionIsomorphism := hRestrict hKernelSynthesis
  exact
    ⟨hKernel, hSecant, hKernelSynthesis, hSecantSynthesis, hRestriction,
      hUnique hRestriction⟩

/-- Paper label: `thm:poisson-lattice-sampling`. This restates the exact lattice constants and the
pointwise Riesz bounds for the integer-translate kernel symbol. -/
theorem paper_poisson_lattice_sampling (A_Z B_Z : ℝ) :
    A_Z = kernelIntegerTranslateLowerBound →
    B_Z = kernelIntegerTranslateUpperBound →
    (∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      A_Z ≤ kernelIntegerTranslateSymbol θ ∧
        kernelIntegerTranslateSymbol θ ≤ B_Z) ∧
      kernelIntegerTranslateSymbol Real.pi = A_Z ∧
      kernelIntegerTranslateSymbol 0 = B_Z := by
  intro hA hB
  subst A_Z
  subst B_Z
  simpa using paper_cdim_kernel_integer_translate_riesz_bounds

end Omega.CircleDimension
