import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Omega.Folding.StableSyntax

namespace Omega.EA.FoldAsSection

open Omega

/-- Fold-as-section: card(X m) = F(m+2) seeds.
    cor:fold-as-section -/
theorem paper_ea_fold_as_section :
    (Fintype.card (X 3) = Nat.fib 5) ∧
    (Fintype.card (X 4) = Nat.fib 6) ∧
    (Fintype.card (X 5) = Nat.fib 7) ∧
    (Nat.fib 5 = 5) ∧ (Nat.fib 6 = 8) ∧ (Nat.fib 7 = 13) := by
  refine ⟨X.card_eq_fib 3, X.card_eq_fib 4, X.card_eq_fib 5, ?_, ?_, ?_⟩
  all_goals simp [Nat.fib_add_two]

end Omega.EA.FoldAsSection
