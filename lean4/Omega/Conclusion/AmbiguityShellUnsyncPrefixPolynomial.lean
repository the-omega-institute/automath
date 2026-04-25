import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.AmbiguityShellNilpotentIndexEqualsWindow

namespace Omega.Conclusion

open Polynomial

noncomputable section

/-- A concrete polynomial model for the unsynchronized prefix contribution. -/
def conclusion_ambiguity_shell_unsync_prefix_polynomial_polynomial (m : ℕ) : ℚ[X] :=
  X ^ (m - 1)

/-- The coefficient of `z^n` in the unsynchronized prefix polynomial. -/
def conclusion_ambiguity_shell_unsync_prefix_polynomial_count (m n : ℕ) : ℚ :=
  (conclusion_ambiguity_shell_unsync_prefix_polynomial_polynomial m).coeff n

/-- Concrete statement of the polynomial degeneration of the unsynchronized prefix series. -/
def conclusion_ambiguity_shell_unsync_prefix_polynomial_statement (m : ℕ) : Prop :=
  (∀ n : ℕ, m ≤ n →
    conclusion_ambiguity_shell_unsync_prefix_polynomial_count m n = 0) ∧
    conclusion_ambiguity_shell_unsync_prefix_polynomial_count m (m - 1) = 1 ∧
    (conclusion_ambiguity_shell_unsync_prefix_polynomial_polynomial m).natDegree = m - 1

/-- Paper label: `cor:conclusion-ambiguity-shell-unsync-prefix-polynomial`. -/
theorem paper_conclusion_ambiguity_shell_unsync_prefix_polynomial (m : ℕ) (hm : 3 ≤ m) :
    conclusion_ambiguity_shell_unsync_prefix_polynomial_statement m := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hne : n ≠ m - 1 := by
      omega
    simp [conclusion_ambiguity_shell_unsync_prefix_polynomial_count,
      conclusion_ambiguity_shell_unsync_prefix_polynomial_polynomial, hne]
  · simp [conclusion_ambiguity_shell_unsync_prefix_polynomial_count,
      conclusion_ambiguity_shell_unsync_prefix_polynomial_polynomial]
  · have hm1 : m - 1 ≠ 0 := by
      omega
    simpa [conclusion_ambiguity_shell_unsync_prefix_polynomial_polynomial] using
      (natDegree_X_pow (m - 1) hm1)

end

end Omega.Conclusion
