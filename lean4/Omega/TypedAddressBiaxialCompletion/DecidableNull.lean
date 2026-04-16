import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompiledReadability
import Omega.TypedAddressBiaxialCompletion.NonNullRequiresThreeAxes
import Omega.TypedAddressBiaxialCompletion.NullExhaustive
import Omega.TypedAddressBiaxialCompletion.UnitarySliceAddressClosure

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for deciding whether a biaxial typed-address readout is `NULL`. The data
collects the unitary-slice closure interface, the `NULL` trichotomy package, and the non-`NULL`
readability/three-axis certificates, together with the two paper-facing conclusion clauses. -/
structure DecidableNullData where
  unitarySliceData : UnitarySliceAddressClosureData
  nullTrichotomyData : TypedAddressNullTrichotomyData
  compiledReadabilityData : CompiledReadabilityData
  threeAxisData : TypedAddressThreeAxisData
  nullHasWitness : Prop
  nonNullHasCertificate : Prop
  readable_h : compiledReadabilityData.readable
  nonNullReadout_h : threeAxisData.nonNullReadout
  deriveNullWitness :
    unitarySliceData.readUSClosed →
      nullTrichotomyData.exhaustive →
        nullHasWitness
  deriveNonNullCertificate :
    unitarySliceData.readUSClosed →
      compiledReadabilityData.readable →
      (compiledReadabilityData.readable ↔
        compiledReadabilityData.addressAdmitted ∧
          compiledReadabilityData.cechObstructionVanishes ∧
            compiledReadabilityData.thresholdsMet ∧
              compiledReadabilityData.certificateFiberNonempty) →
      threeAxisData.nonNullReadout →
      (threeAxisData.nonNullReadout →
        threeAxisData.visibleAxisPassed ∧
          threeAxisData.residueAxisPassed ∧
            threeAxisData.modeAxisPassed) →
      nonNullHasCertificate

/-- The unitary-slice closure law, the `NULL` trichotomy, and the existing non-`NULL`
readability/axis packages combine into a decidability package: either one extracts a `NULL`
witness or one extracts a non-`NULL` certificate.
    prop:typed-address-biaxial-completion-decidable-null -/
theorem paper_typed_address_biaxial_completion_decidable_null (D : DecidableNullData) :
    D.nullHasWitness ∧ D.nonNullHasCertificate := by
  have hUnitary : D.unitarySliceData.readUSClosed :=
    paper_typed_address_biaxial_completion_unitary_slice_address_closure D.unitarySliceData
  have hNullExhaustive : D.nullTrichotomyData.exhaustive := D.nullTrichotomyData.exhaustiveWitness
  have hReadable :
      D.compiledReadabilityData.readable ↔
        D.compiledReadabilityData.addressAdmitted ∧
          D.compiledReadabilityData.cechObstructionVanishes ∧
            D.compiledReadabilityData.thresholdsMet ∧
              D.compiledReadabilityData.certificateFiberNonempty :=
    paper_typed_address_biaxial_completion_compiled_readability_readable
      D.compiledReadabilityData
  have hAxes :
      D.threeAxisData.nonNullReadout →
        D.threeAxisData.visibleAxisPassed ∧
          D.threeAxisData.residueAxisPassed ∧
            D.threeAxisData.modeAxisPassed :=
    paper_typed_address_biaxial_completion_nonnull_requires_three_axes D.threeAxisData
  exact
    ⟨D.deriveNullWitness hUnitary hNullExhaustive,
      D.deriveNonNullCertificate hUnitary D.readable_h hReadable D.nonNullReadout_h hAxes⟩

end Omega.TypedAddressBiaxialCompletion
