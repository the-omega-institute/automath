import Mathlib.Tactic
import Omega.GU.TerminalCutProjectToFoldHist

namespace Omega.GU

/-- Paper label: `cor:terminal-rotation-window-prototype`.
The implementation-independent window-6 invariant is exactly the audited second component of the
cut-project-to-fold-hist theorem. -/
theorem paper_terminal_rotation_window_prototype : terminalCutProjectWindow6Invariant := by
  exact paper_terminal_cut_project_to_fold_hist.2

/-- Small abstract interface for the one-dimensional rotation-plus-window prototype. The rotation
is recorded by its step and cut position, while the finite window and audited local-block
histogram supply the finite observable interface. -/
structure TerminalRotationWindowPrototypeData where
  rotationStep : ℚ
  windowCut : ℚ
  windowLength : ℕ
  observedBlockCount : ℕ
  observedBlockCount_le : observedBlockCount ≤ 2 ^ windowLength

namespace TerminalRotationWindowPrototypeData

/-- Window readouts are Boolean blocks of a fixed finite length. -/
abbrev windowReadoutType (D : TerminalRotationWindowPrototypeData) : Type :=
  Fin D.windowLength → Bool

/-- The audited local-block histogram is indexed by the finite set of observed blocks. -/
abbrev blockAuditType (D : TerminalRotationWindowPrototypeData) : Type :=
  Fin D.observedBlockCount

/-- A finite window determines exactly the local Boolean blocks that can be read out by the
rotation-plus-window scanner. -/
def rotationWindowReadout (D : TerminalRotationWindowPrototypeData) : Prop :=
  Fintype.card (Fin D.windowLength → Bool) = 2 ^ D.windowLength ∧
    D.observedBlockCount ≤ Fintype.card (Fin D.windowLength → Bool)

/-- The histogram side is finite and therefore provides an auditable baseline for comparing the
geometric scan with the folding-side block statistics. -/
def finiteBlockAuditBaseline (D : TerminalRotationWindowPrototypeData) : Prop :=
  Fintype.card (Fin D.windowLength) = D.windowLength ∧
    Fintype.card (Fin D.observedBlockCount) = D.observedBlockCount

end TerminalRotationWindowPrototypeData

open TerminalRotationWindowPrototypeData

/-- Auxiliary interface theorem retaining the finite-window block-audit formalization used during
this round. -/
theorem paper_terminal_rotation_window_prototype_interface (D : TerminalRotationWindowPrototypeData)
    : D.rotationWindowReadout ∧ D.finiteBlockAuditBaseline := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp
    · simpa using D.observedBlockCount_le
  · refine ⟨by simp, by simp⟩

end Omega.GU
