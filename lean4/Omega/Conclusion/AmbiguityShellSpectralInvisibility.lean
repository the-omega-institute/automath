import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Omega.Conclusion.AmbiguityShellJordanChainGraphLift
import Omega.Folding.SyncDelay

namespace Omega.Conclusion

open Matrix

/-- The synchronizing budget attached to the ambiguity-shell model. -/
def ambiguityShellSyncBudget (m : ℕ) : ℕ :=
  m - 1

lemma ambiguityShellNilpotent_eq_zero : ambiguityShellNilpotent = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [ambiguityShellNilpotent]

lemma ambiguityShellTraceInvisible (n : ℕ) :
    (ambiguityShellNilpotent ^ (n + 1)).trace = 0 := by
  simp [ambiguityShellNilpotent_eq_zero]

lemma ambiguityShellDetInvisible :
    (((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1) := by
  native_decide

lemma ambiguityShellSyncBudgetExact (m : ℕ) (hm : 3 ≤ m) :
    ambiguityShellSyncBudget m = m - 1 ∧ ambiguityShellSyncBudget m < m := by
  rcases Omega.Folding.SyncDelay.paper_fold_sync_delay with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsync⟩
  refine ⟨rfl, ?_⟩
  simpa [ambiguityShellSyncBudget] using hsync m hm

/-- The `1 × 1` ambiguity shell is nilpotent, so every positive trace contribution vanishes and
the determinant factor `(I - N)` stays equal to `1`; the synchronizing budget is exactly `m - 1`,
with the strict budget gap supplied by the existing sync-delay theorem.
    thm:conclusion-ambiguity-shell-spectral-invisibility -/
theorem paper_conclusion_ambiguity_shell_spectral_invisibility :
    (∀ n : ℕ, (ambiguityShellNilpotent ^ (n + 1)).trace = 0) ∧
    (((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1) ∧
    (∀ m : ℕ, 3 ≤ m → ambiguityShellSyncBudget m = m - 1 ∧ ambiguityShellSyncBudget m < m) := by
  exact ⟨ambiguityShellTraceInvisible, ambiguityShellDetInvisible, ambiguityShellSyncBudgetExact⟩

end Omega.Conclusion
