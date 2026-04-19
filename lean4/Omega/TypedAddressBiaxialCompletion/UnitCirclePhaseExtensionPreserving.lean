namespace Omega.TypedAddressBiaxialCompletion

/-- The chapter-local record axis used to externalize the invisible degrees of freedom. -/
def unitCirclePhaseRecordAxis (Ω : Type _) : Type _ :=
  Ω

/-- The trivial record field is the identity on the source space. -/
def unitCirclePhaseRecord (Ω : Type _) : Ω → unitCirclePhaseRecordAxis Ω :=
  id

/-- Extend a partial observation by pairing it with the record field. -/
def unitCirclePhaseExtendedObservation {Ω X : Type _} (π : Ω → X) :
    Ω → X × unitCirclePhaseRecordAxis Ω :=
  fun ω => (π ω, unitCirclePhaseRecord Ω ω)

/-- Any partial observation becomes injective after adjoining the identity record axis.
    prop:unit-circle-phase-extension-preserving -/
theorem paper_unit_circle_phase_extension_preserving {Ω X : Type _} (π : Ω → X) :
    Function.Injective (unitCirclePhaseExtendedObservation π) := by
  intro ω ω' h
  exact congrArg Prod.snd h

end Omega.TypedAddressBiaxialCompletion
