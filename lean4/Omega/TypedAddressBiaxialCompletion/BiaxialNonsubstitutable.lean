import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- The visible quotient witness for a complete phase extension. -/
structure CompletePhaseVisibleQuotient where
  circleRank : ℕ

/-- The profinite kernel witness for a complete phase extension. -/
structure CompletePhaseKernel where
  primeSupport : Finset ℕ
  registerRank : ℕ

/-- Chapter-local record for a complete phase extension. -/
structure CompletePhaseExtension where
  visibleQuotient : CompletePhaseVisibleQuotient
  kernelWitness : CompletePhaseKernel

/-- The two biaxial coordinates live on different structural layers of the extension. -/
inductive CompletePhaseLayer
  | visibleQuotient
  | kernel
deriving DecidableEq

/-- The phase coordinate is the visible circle rank of the quotient. -/
def phaseAxis (E : CompletePhaseExtension) : ℕ :=
  E.visibleQuotient.circleRank

/-- The ledger coordinate is the register rank of the kernel witness. -/
def ledgerAxis (E : CompletePhaseExtension) : ℕ :=
  E.kernelWitness.registerRank

/-- The phase axis is read from the visible quotient layer. -/
def phaseAxisLayer (_E : CompletePhaseExtension) : CompletePhaseLayer :=
  .visibleQuotient

/-- The ledger axis is read from the kernel layer. -/
def ledgerAxisLayer (_E : CompletePhaseExtension) : CompletePhaseLayer :=
  .kernel

/-- The visible quotient alone determines the phase axis. -/
def phaseAxisDependsOnlyOnVisibleQuotient (E : CompletePhaseExtension) : Prop :=
  phaseAxis E = E.visibleQuotient.circleRank

/-- The profinite kernel alone determines the ledger axis. -/
def ledgerAxisDependsOnlyOnKernel (E : CompletePhaseExtension) : Prop :=
  ledgerAxis E = E.kernelWitness.registerRank

/-- Because the two coordinates live on different layers, the complete-phase invariant has to be
kept as an ordered pair. -/
def requiresOrderedPair (E : CompletePhaseExtension) : Prop :=
  phaseAxisLayer E ≠ ledgerAxisLayer E

/-- Paper label: `prop:typed-address-biaxial-completion-biaxial-nonsubstitutable`. -/
theorem paper_typed_address_biaxial_completion_biaxial_nonsubstitutable
    (E : CompletePhaseExtension) :
    phaseAxisDependsOnlyOnVisibleQuotient E ∧
      ledgerAxisDependsOnlyOnKernel E ∧
      requiresOrderedPair E := by
  refine ⟨rfl, rfl, ?_⟩
  intro hLayer
  cases hLayer

end Omega.TypedAddressBiaxialCompletion
