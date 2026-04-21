import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Omega.Conclusion.AmbiguityShellJordanChainGraphLift
import Omega.Folding.SyncDelay

namespace Omega.Conclusion

open Matrix

/-- Paper label: `thm:conclusion-ambiguity-shell-zeta-sync-splitting`.
The ambiguity shell is the `1 × 1` nilpotent block `0`, so its determinant contribution is `1`,
all positive-length periodic trace data vanish, and the synchronizing contribution is exactly the
existing delay package `m - 1 < m` for `m ≥ 3`. -/
theorem paper_conclusion_ambiguity_shell_zeta_sync_splitting :
    (((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1) ∧
      (∀ n : ℕ, (ambiguityShellNilpotent ^ (n + 1)).trace = 0) ∧
      (∀ m : ℕ, 3 ≤ m → m - 1 < m) := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro n
    have hzero : ambiguityShellNilpotent = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [ambiguityShellNilpotent]
    simp [hzero]
  · intro m hm
    rcases Omega.Folding.SyncDelay.paper_fold_sync_delay with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsync⟩
    exact hsync m hm

end Omega.Conclusion
