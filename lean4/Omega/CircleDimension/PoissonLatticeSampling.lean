import Mathlib.Tactic

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

end Omega.CircleDimension
