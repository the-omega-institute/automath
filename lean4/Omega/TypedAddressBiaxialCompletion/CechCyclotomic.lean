import Mathlib.Tactic
import Omega.CircleDimension.CechCyclotomicQuantization

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address wrapper around the chapter-local Čech--cyclotomic quantization package.
    thm:typed-address-biaxial-completion-cech-cyclotomic -/
theorem paper_typed_address_biaxial_completion_cech_cyclotomic
    (h : Omega.CircleDimension.CechCyclotomicQuantizationData) :
    h.obstructionGivesPrimitiveRootOrbit ∧ h.primitiveRootOrbitForcesNull := by
  simpa using Omega.CircleDimension.paper_cdim_cech_cyclotomic_quantization h

end Omega.TypedAddressBiaxialCompletion
