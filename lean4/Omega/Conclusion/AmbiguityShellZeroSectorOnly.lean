import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Omega.Conclusion.AmbiguityShellNilpotentIndexEqualsWindow
import Omega.Conclusion.AmbiguityShellSpectralInvisibility

namespace Omega.Conclusion

open Matrix

/-- The ambiguity shell only contributes at the zero sector: nonzero spectral traces and determinant
data are invisible, while a sharp nilpotent tower has zero-sector height exactly its window. -/
def conclusion_ambiguity_shell_zero_sector_only_statement (m : ℕ) : Prop :=
  (∀ n : ℕ, (ambiguityShellNilpotent ^ (n + 1)).trace = 0) ∧
    (((1 : Matrix (Fin 1) (Fin 1) ℚ) - ambiguityShellNilpotent).det = 1) ∧
    (∀ N : Matrix (Fin m) (Fin m) ℚ, 1 ≤ m → N ^ m = 0 → N ^ (m - 1) ≠ 0 →
      ∀ r : ℕ, 1 ≤ r → N ^ r = 0 → m ≤ r) ∧
    ambiguityShellSyncBudget m = m - 1 ∧
    ambiguityShellSyncBudget m < m

/-- Paper label: `thm:conclusion-ambiguity-shell-zero-sector-only`. -/
theorem paper_conclusion_ambiguity_shell_zero_sector_only (m : ℕ) (hm : 3 ≤ m) :
    conclusion_ambiguity_shell_zero_sector_only_statement m := by
  rcases paper_conclusion_ambiguity_shell_spectral_invisibility with
    ⟨htrace, hdet, hbudget⟩
  rcases hbudget m hm with ⟨hbudget_eq, hbudget_lt⟩
  refine ⟨htrace, hdet, ?_, hbudget_eq, hbudget_lt⟩
  intro N hm1 hpow hsharp r hr hz
  exact paper_conclusion_ambiguity_shell_nilpotent_index_equals_window m N hm1 hpow hsharp r hr hz

end Omega.Conclusion
