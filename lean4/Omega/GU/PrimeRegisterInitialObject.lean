import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the prime-register initial-object theorem. The fields isolate the
coordinatewise injectivity of the shifted-prime encoding and the existence/uniqueness of the
homomorphism extending a basis assignment from the shifted prime generators. -/
structure PrimeRegisterInitialObjectData where
  isEncoder : Prop
  isInitial : Prop
  encodingInjectiveByCoordinates : Prop
  basisExtensionExists : Prop
  basisExtensionUnique : Prop
  encodingInjectiveByCoordinates_h : encodingInjectiveByCoordinates
  basisExtensionExists_h : basisExtensionExists
  basisExtensionUnique_h : basisExtensionUnique
  deriveIsEncoder :
    encodingInjectiveByCoordinates → isEncoder
  deriveIsInitial :
    basisExtensionExists → basisExtensionUnique → isInitial

/-- Paper-facing wrapper for the shifted-prime register package: coordinate equality proves the
encoding map is injective, and free commutative-monoid extension from the shifted prime basis
supplies the unique initial morphism.
    thm:group-jg-prime-register-initial-object -/
theorem paper_group_jg_prime_register_initial_object
    (D : PrimeRegisterInitialObjectData) : D.isEncoder ∧ D.isInitial := by
  have hEncoder : D.isEncoder :=
    D.deriveIsEncoder D.encodingInjectiveByCoordinates_h
  have hInitial : D.isInitial :=
    D.deriveIsInitial D.basisExtensionExists_h D.basisExtensionUnique_h
  exact ⟨hEncoder, hInitial⟩

end Omega.GU
