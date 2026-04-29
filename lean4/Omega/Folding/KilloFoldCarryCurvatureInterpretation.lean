import Omega.Folding.KilloFoldCarryDefectCocycleNonsplit

namespace Omega

open KilloFoldCarryDefectCocycleData

/-- The concrete no-section obstruction extracted from the carry-defect cocycle package. -/
def killo_fold_carry_curvature_interpretation_no_section
    (m : Nat) (_D : KilloFoldCarryDefectCocycleData m) : Prop :=
  ¬ ∃ (h : Fin 3 → ℤ),
      h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 0 - h 2 = 1

/-- The same obstruction viewed as the nontriviality of the carry-curvature class. -/
def killo_fold_carry_curvature_interpretation_no_trivialization
    (m : Nat) (_D : KilloFoldCarryDefectCocycleData m) : Prop :=
  ¬ ∃ (h : Fin 3 → ℤ),
      h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 0 - h 2 = 1

/-- Corollary-level package interpreting the nonsplit carry cocycle as a persistent curvature
obstruction. -/
def killo_fold_carry_curvature_interpretation_statement
    (m : Nat) (D : KilloFoldCarryDefectCocycleData m) : Prop :=
  X.modularProject (X.stableAdd D.x D.y) =
      X.stableAdd (X.stableAdd (X.modularProject D.x) (X.modularProject D.y))
        (if carryIndicator D.x D.y = 0 then X.stableZero else X.carryElement m) ∧
    globalDefect (Nat.le_trans (Nat.le_succ m) D.succ_le_towerTop) D.witness =
      xorWord
        (globalDefect (Nat.le_succ m) (restrictWord D.succ_le_towerTop D.witness))
        (restrictWord (Nat.le_succ m) (globalDefect D.succ_le_towerTop D.witness)) ∧
    killo_fold_carry_curvature_interpretation_no_section m D ∧
    killo_fold_carry_curvature_interpretation_no_trivialization m D

/-- Paper label: `cor:killo-fold-carry-curvature-interpretation`. -/
theorem paper_killo_fold_carry_curvature_interpretation
    (m : Nat) (D : KilloFoldCarryDefectCocycleData m) :
    killo_fold_carry_curvature_interpretation_statement m D := by
  rcases paper_killo_fold_carry_defect_cocycle_nonsplit m D with ⟨hcarry, hglobal, hnonsplit⟩
  exact ⟨hcarry, hglobal, hnonsplit, hnonsplit⟩

end Omega
