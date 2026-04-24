import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-visible-finite-type-fibonacci-complete-audit`.
Positive finite-type defect is equivalent both to the existence of a failing Toeplitz block and,
after Fibonacci localization, to the existence of a failing Fibonacci-indexed block. -/
theorem paper_conclusion_visible_finite_type_fibonacci_complete_audit
    (κ : ℕ) (failsPsd : ℕ → Prop) (hDefect : 0 < κ ↔ ∃ N, failsPsd N)
    (hFib : ∀ {N}, failsPsd N → ∃ k, N ≤ Nat.fib k ∧ failsPsd (Nat.fib k)) :
    ((0 < κ) ↔ ∃ N, failsPsd N) ∧ ((∃ N, failsPsd N) ↔ ∃ k, failsPsd (Nat.fib k)) := by
  refine ⟨hDefect, ?_⟩
  constructor
  · rintro ⟨N, hN⟩
    rcases hFib hN with ⟨k, -, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨Nat.fib k, hk⟩

end Omega.Conclusion
