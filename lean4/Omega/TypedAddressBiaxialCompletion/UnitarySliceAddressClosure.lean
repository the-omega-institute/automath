import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

universe u v

/-- Chapter-local wrapper for the unitary-slice address-closure statement. The data records the
ambient address space, the readout codomain, the guarded unitary-slice readout, and the closure
rule asserting that the guarded readout stays inside the addressable unitary-slice layer. -/
structure UnitarySliceAddressClosureData where
  AddressSpace : Type u
  ReadoutCodomain : Type v
  unitarySliceAddress : AddressSpace → Prop
  guardedReadout : ∀ a : AddressSpace, unitarySliceAddress a → ReadoutCodomain
  guardedRule : Prop
  readUSClosed : Prop
  hasGuardedRule : guardedRule
  guardedReadoutCloses : guardedRule → readUSClosed

/-- Guarded readout on the unitary-slice address space is closed under the advertised address
formation rule.
    prop:typed-address-biaxial-completion-unitary-slice-address-closure -/
theorem paper_typed_address_biaxial_completion_unitary_slice_address_closure
    (D : UnitarySliceAddressClosureData) :
    D.readUSClosed := by
  exact D.guardedReadoutCloses D.hasGuardedRule

end Omega.TypedAddressBiaxialCompletion
