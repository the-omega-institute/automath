import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompletenessGapAudit
import Omega.TypedAddressBiaxialCompletion.GlobalizationFlatness
import Omega.TypedAddressBiaxialCompletion.NullFiber
import Omega.TypedAddressBiaxialCompletion.OffsliceDichotomy
import Omega.TypedAddressBiaxialCompletion.ReadableFiber

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local data for the compiled readability criterion. The `readsNonNull` field preserves
the direct readout contract, while `readable` and its implications record the already-audited
readable, obstruction, threshold, and fiber witnesses used in the chapter. -/
structure CompiledReadabilityData where
  readsNonNull : Prop
  readable : Prop
  addressAdmitted : Prop
  cechObstructionVanishes : Prop
  thresholdsMet : Prop
  certificateFiberNonempty : Prop
  readoutContract :
    readsNonNull ↔
      addressAdmitted ∧ cechObstructionVanishes ∧ thresholdsMet ∧ certificateFiberNonempty
  readable_implies_addressAdmitted : readable → addressAdmitted
  readable_implies_cechObstructionVanishes : readable → cechObstructionVanishes
  readable_implies_thresholdsMet : readable → thresholdsMet
  readable_implies_certificateFiberNonempty : readable → certificateFiberNonempty
  compiledChecks_imply_readable :
    addressAdmitted →
      cechObstructionVanishes →
        thresholdsMet →
          certificateFiberNonempty →
            readable

/-- A compiled readout is non-`NULL` exactly when the address is admitted, the Cech obstruction
vanishes, the threshold checks pass, and the certificate fiber is inhabited.
    prop:typed-address-biaxial-completion-compiled-readability -/
theorem paper_typed_address_biaxial_completion_compiled_readability (h : CompiledReadabilityData) :
    h.readsNonNull ↔
      h.addressAdmitted ∧
        h.cechObstructionVanishes ∧ h.thresholdsMet ∧ h.certificateFiberNonempty := by
  simpa using h.readoutContract

/-- Wrapper form of compiled readability expressed in terms of the chapter-local `readable`
output. -/
theorem paper_typed_address_biaxial_completion_compiled_readability_readable
    (D : CompiledReadabilityData) :
    D.readable ↔
      D.addressAdmitted ∧
        D.cechObstructionVanishes ∧ D.thresholdsMet ∧ D.certificateFiberNonempty := by
  constructor
  · intro hReadable
    exact
      ⟨D.readable_implies_addressAdmitted hReadable,
        D.readable_implies_cechObstructionVanishes hReadable,
        D.readable_implies_thresholdsMet hReadable,
        D.readable_implies_certificateFiberNonempty hReadable⟩
  · rintro ⟨hAddress, hCech, hThresholds, hFiber⟩
    exact D.compiledChecks_imply_readable hAddress hCech hThresholds hFiber

end Omega.TypedAddressBiaxialCompletion
