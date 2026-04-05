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

/-- The three tail offsets {F_8, F_9, F_10} = {21, 34, 55}.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem fold6_tail_offsets :
    Nat.fib 8 = 21 ∧ Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- GUT top-term Fibonacci alignment: SU(5)/SO(10)/E_6.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem gut_top_fibonacci_terms :
    (24 = Nat.fib 8 + Nat.fib 4) ∧
    (45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4) ∧
    (78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- Tail offsets = |X_6|, |X_7|, |X_8|.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem fold6_tail_offsets_are_card_X :
    Nat.fib 8 = Fintype.card (X 6) ∧
    Nat.fib 9 = Fintype.card (X 7) ∧
    Nat.fib 10 = Fintype.card (X 8) := by
  exact ⟨(X.card_eq_fib 6).symm, (X.card_eq_fib 7).symm, (X.card_eq_fib 8).symm⟩

/-- The resonance gap: |X_8| - |X_6| = |X_7|.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem fold6_resonance_gap :
    Fintype.card (X 8) - Fintype.card (X 6) = Fintype.card (X 7) := by
  rw [X.card_X_eight, X.card_X_six, X.card_X_seven]

/-- GUT top-term Fibonacci alignment.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem paper_gut_fibonacci_alignment :
    (24 = Nat.fib 8 + Nat.fib 4) ∧
    (45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4) ∧
    (78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3) ∧
    Nat.fib 8 = 21 ∧ Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 :=
  ⟨gut_top_fibonacci_terms.1, gut_top_fibonacci_terms.2.1, gut_top_fibonacci_terms.2.2,
   fold6_tail_offsets.1, fold6_tail_offsets.2.1, fold6_tail_offsets.2.2⟩

/-- SU(5) count closure: |X_6| + |X_2| = 24 = 4!.
    cor:su5-21-plus-3-closure -/
theorem paper_su5_count_closure :
    Fintype.card (X 6) + Fintype.card (X 2) = 24 ∧
    Nat.fib 8 = Fintype.card (X 6) ∧
    Nat.fib 4 = Fintype.card (X 2) ∧
    Nat.factorial 4 = 24 := by
  refine ⟨by rw [X.card_X_six, X.card_X_two], su5_count_closure_fib.1,
    su5_count_closure_fib.2.1, by native_decide⟩

end Omega.GU
