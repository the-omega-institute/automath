import Omega.Folding.StableSyntax
import Omega.Folding.FiberArithmetic
import Mathlib.Tactic

open Omega X

namespace Omega.GU

/-- cor:su5-21-plus-3-closure -/
theorem su5_count_closure_X6_X2 :
    24 = Fintype.card (X 6) + Fintype.card (X 2) := by
  rw [X.card_X_six, X.card_X_two]

/-- cor:su5-21-plus-3-closure -/
theorem su5_count_closure_fib :
    Nat.fib 8 = Fintype.card (X 6) ∧
    Nat.fib 4 = Fintype.card (X 2) ∧
    24 = Fintype.card (X 6) + Fintype.card (X 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [X.card_eq_fib]
  · rw [X.card_eq_fib]
  · rw [X.card_X_six, X.card_X_two]

end Omega.GU
