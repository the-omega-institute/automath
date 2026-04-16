import Omega.CircleDimension.RegisterCircleModpFormula

namespace Omega.TypedAddressBiaxialCompletion

open Omega.CircleDimension

/-- Typed-address packaging of the circle-dimension mod-`p` formula. The inherited fields are the
profinite kernel data; the extra fields record the hypotheses needed by the circle-dimension
wrapper theorem. -/
structure TypedAddressPcdimModpData extends RegisterCircleModpData where
  hSurjection : pcdim = zhatSurjectionDim
  hSylowSup : pcdim = registerCirclePrimeSup primes sylowPcdim
  hSylowModp : ∀ p ∈ primes, modpDim p = sylowModpDim p
  hGenerator : ∀ p ∈ primes, sylowPcdim p = sylowModpDim p

/-- The typed-address profinite kernel dimension is the supremum of the mod-`p` generator counts.
    prop:typed-address-biaxial-completion-pcdim-modp -/
theorem paper_typed_address_biaxial_completion_pcdim_modp
    (K : TypedAddressPcdimModpData) : K.pcdim = registerCirclePrimeSup K.primes K.modpDim := by
  obtain ⟨_, hModp, _⟩ :=
    paper_cdim_register_circle_modp_formula
      (K := K.toRegisterCircleModpData) K.hSurjection K.hSylowSup K.hSylowModp K.hGenerator
  exact hModp

end Omega.TypedAddressBiaxialCompletion
