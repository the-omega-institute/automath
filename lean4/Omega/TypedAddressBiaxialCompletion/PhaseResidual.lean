import Omega.CircleDimension.VisiblePhaseResidualTriviality

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address name for the chapter-local obstruction class. -/
def typedAddressObstructionClass : ℤ :=
  Omega.CircleDimension.obstruction_class

/-- Typed-address pushforward of the obstruction class to the visible phase. -/
def typedAddressPushforwardVisibleClass (c : ℤ) : ℤ :=
  Omega.CircleDimension.pushforward_visible_class c

/-- Typed-address visible residual class. -/
def typedAddressVisibleResidualClass : ℤ :=
  typedAddressPushforwardVisibleClass typedAddressObstructionClass

/-- Typed-address visible-phase triviality predicate. -/
def typedAddressVisiblePhaseTrivializable : Prop :=
  typedAddressVisibleResidualClass = 0

/-- Paper-facing typed-address interface theorem for the visible phase residual package. -/
theorem paper_typed_address_biaxial_completion_phase_residual :
    typedAddressVisibleResidualClass =
      typedAddressPushforwardVisibleClass typedAddressObstructionClass ∧
      (typedAddressVisibleResidualClass = 0 ↔ typedAddressVisiblePhaseTrivializable) := by
  simpa [typedAddressVisibleResidualClass, typedAddressPushforwardVisibleClass,
    typedAddressObstructionClass, typedAddressVisiblePhaseTrivializable] using
    Omega.CircleDimension.paper_cdim_visible_phase_residual_triviality

end Omega.TypedAddressBiaxialCompletion
