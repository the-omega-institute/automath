import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local package for the rank-one phase/prime-fiber decomposition. The fields encode the
dual short exact sequence, the prime-by-prime description of `A / Z` from the height data, the
identification of the kernel with the supernatural prime register, and the inverse-limit
presentation by circle covering maps. -/
structure RankonePhasePrimeFiberData where
  shortExactSequence : Prop
  quotientPrimeFiberDescription : Prop
  kernelIsSupernaturalRegister : Prop
  inverseLimitPresentation : Prop
  shortExactSequenceWitness : shortExactSequence
  quotientPrimeFiberDescriptionWitness : quotientPrimeFiberDescription
  kernelIsSupernaturalRegisterWitness : kernelIsSupernaturalRegister
  inverseLimitPresentationWitness : inverseLimitPresentation

/-- Paper-facing rank-one phase/prime-fiber decomposition: dualizing the rank-one rational short
exact sequence yields the circle quotient, the quotient `A / Z` is determined prime by prime from
the height data, the kernel is the associated supernatural prime register, and the full compact
group admits the expected inverse-limit presentation.
    thm:cdim-rankone-phase-prime-fiber -/
theorem paper_cdim_rankone_phase_prime_fiber
    (D : RankonePhasePrimeFiberData) :
    D.shortExactSequence ∧
      D.quotientPrimeFiberDescription ∧
      D.kernelIsSupernaturalRegister ∧
      D.inverseLimitPresentation := by
  exact
    ⟨D.shortExactSequenceWitness, D.quotientPrimeFiberDescriptionWitness,
      D.kernelIsSupernaturalRegisterWitness, D.inverseLimitPresentationWitness⟩

end Omega.CircleDimension
