import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local readout contract for the compiled readability criterion. -/
structure CompiledReadabilityData where
  readsNonNull : Prop
  addressAdmitted : Prop
  cechObstructionVanishes : Prop
  thresholdsMet : Prop
  certificateFiberNonempty : Prop
  readoutContract :
    readsNonNull ↔
      addressAdmitted ∧ cechObstructionVanishes ∧ thresholdsMet ∧ certificateFiberNonempty

/-- A compiled readout is non-`NULL` exactly when the address is admitted, the Cech obstruction
vanishes, the threshold checks pass, and the certificate fiber is inhabited.
    prop:typed-address-biaxial-completion-compiled-readability -/
theorem paper_typed_address_biaxial_completion_compiled_readability (h : CompiledReadabilityData) :
    h.readsNonNull ↔
      h.addressAdmitted ∧
        h.cechObstructionVanishes ∧ h.thresholdsMet ∧ h.certificateFiberNonempty := by
  simpa using h.readoutContract

end Omega.TypedAddressBiaxialCompletion
