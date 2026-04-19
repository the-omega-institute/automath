import Omega.Folding.Defect
import Omega.Folding.MismatchLanguage
import Omega.Folding.ModularTower

namespace Omega

/-- Concrete data for the carry-defect cocycle package on a Fibonacci fold tower. The fields record
the adjacent-scale carry witness and a higher-resolution word used for the global cocycle witness. -/
structure KilloFoldCarryDefectCocycleData (m : Nat) where
  x : X (m + 1)
  y : X (m + 1)
  towerTop : Nat
  succ_le_towerTop : m + 1 ≤ towerTop
  witness : Word towerTop

namespace KilloFoldCarryDefectCocycleData

/-- Paper-facing package: the adjacent-scale carry defect is the modular-project correction term,
the global defect satisfies the cocycle identity across the Fibonacci tower, and the resulting
coherence class is witnessed to be non-split by the mismatch-language obstruction.
    thm:killo-fold-carry-defect-cocycle-nonsplit -/
def cocycleNonsplit {m : Nat} (D : KilloFoldCarryDefectCocycleData m) : Prop :=
  X.modularProject (X.stableAdd D.x D.y) =
      X.stableAdd (X.stableAdd (X.modularProject D.x) (X.modularProject D.y))
        (if carryIndicator D.x D.y = 0 then X.stableZero else X.carryElement m) ∧
    globalDefect (Nat.le_trans (Nat.le_succ m) D.succ_le_towerTop) D.witness =
      xorWord
        (globalDefect (Nat.le_succ m) (restrictWord D.succ_le_towerTop D.witness))
        (restrictWord (Nat.le_succ m) (globalDefect D.succ_le_towerTop D.witness)) ∧
    ¬ ∃ (h : Fin 3 → ℤ),
        h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 0 - h 2 = 1

end KilloFoldCarryDefectCocycleData

open KilloFoldCarryDefectCocycleData

theorem paper_killo_fold_carry_defect_cocycle_nonsplit (m : Nat)
    (D : KilloFoldCarryDefectCocycleData m) : D.cocycleNonsplit := by
  refine ⟨X.modularProject_stableAdd_carry D.x D.y, ?_, paper_mismatch_label_non_coboundary⟩
  exact globalDefect_poincare_band D.succ_le_towerTop D.witness

end Omega
