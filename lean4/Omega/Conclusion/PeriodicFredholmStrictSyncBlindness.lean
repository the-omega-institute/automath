import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Omega.Conclusion.AmbiguityShellZetaSyncSplitting

namespace Omega.Conclusion

open Matrix

/-- Concrete consequence data for the strict sync-blindness corollary. The periodic and Fredholm
channels are the determinant/trace data of the nilpotent ambiguity shell; the synchronizing budget
is recorded separately at a level `m ≥ 3`. -/
structure conclusion_periodic_fredholm_strict_sync_blindness_Data where
  syncLevel : ℕ
  hSyncLevel : 3 ≤ syncLevel
  syncBudget : ℕ
  hSyncBudget : syncBudget = syncLevel - 1

namespace conclusion_periodic_fredholm_strict_sync_blindness_Data

/-- Determinant, zeta, primitive-count, and entropy-type periodic data see no nonzero shell
contribution. -/
def periodicDataBlind (_D : conclusion_periodic_fredholm_strict_sync_blindness_Data) : Prop :=
  (((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1) ∧
    (∀ n : ℕ, (ambiguityShellNilpotent ^ (n + 1)).trace = 0)

/-- Fredholm data depending on the same determinant law is equally blind to the shell. -/
def fredholmDataBlind (_D : conclusion_periodic_fredholm_strict_sync_blindness_Data) : Prop :=
  ((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1

/-- The synchronization budget must be kept as a separate ambiguity-shell record. -/
def requiresAmbiguityShellRecord
    (D : conclusion_periodic_fredholm_strict_sync_blindness_Data) : Prop :=
  D.syncBudget < D.syncLevel

end conclusion_periodic_fredholm_strict_sync_blindness_Data

/-- Paper label: `cor:conclusion-periodic-fredholm-strict-sync-blindness`.
The verified zeta/sync splitting theorem supplies determinant and trace blindness, while the
separate ambiguity-shell delay witness supplies the strict synchronization budget. -/
theorem paper_conclusion_periodic_fredholm_strict_sync_blindness
    (D : conclusion_periodic_fredholm_strict_sync_blindness_Data) :
    D.periodicDataBlind ∧ D.fredholmDataBlind ∧ D.requiresAmbiguityShellRecord := by
  rcases paper_conclusion_ambiguity_shell_zeta_sync_splitting with ⟨hdet, htrace, hsync⟩
  refine ⟨⟨hdet, htrace⟩, hdet, ?_⟩
  rw [conclusion_periodic_fredholm_strict_sync_blindness_Data.requiresAmbiguityShellRecord,
    D.hSyncBudget]
  exact hsync D.syncLevel D.hSyncLevel

end Omega.Conclusion
