import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Concrete unit-circle phase data for the standard ledger prototype. The visible ledger is the
rank, while the register ledger collapses to `0` exactly in the trivial-modulus case. -/
structure CompletePhaseStandardLedgerData where
  rank : ℕ
  modulus : ℕ

namespace CompletePhaseStandardLedgerData

/-- The visible ledger rank of the standard prototype. -/
def visibleLedger (D : CompletePhaseStandardLedgerData) : ℕ :=
  D.rank

/-- The supernatural modulus is trivial exactly when the stored modulus vanishes. -/
def modulusTrivial (D : CompletePhaseStandardLedgerData) : Prop :=
  D.modulus = 0

/-- The register side matches the visible rank except in the trivial-modulus collapse. -/
def registerLedger (D : CompletePhaseStandardLedgerData) : ℕ :=
  if D.modulus = 0 then 0 else D.rank

end CompletePhaseStandardLedgerData

open CompletePhaseStandardLedgerData

/-- Paper label: `prop:unit-circle-complete-phase-standard-ledger`. -/
theorem paper_unit_circle_complete_phase_standard_ledger (D : CompletePhaseStandardLedgerData) :
    D.visibleLedger = D.rank ∧ (¬ D.modulusTrivial → D.registerLedger = D.rank) ∧
      (D.modulusTrivial → D.registerLedger = 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    unfold CompletePhaseStandardLedgerData.modulusTrivial at h
    simp [CompletePhaseStandardLedgerData.registerLedger, h]
  · intro h
    unfold CompletePhaseStandardLedgerData.modulusTrivial at h
    simp [CompletePhaseStandardLedgerData.registerLedger, h]

end Omega.UnitCirclePhaseArithmetic
