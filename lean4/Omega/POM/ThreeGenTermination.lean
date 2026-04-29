import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

namespace Omega.POM

open Prod.Lex

/-- The three generators used by the publication-facing rewrite system. -/
abbrev pom_three_gen_termination_token := Fin 3

/-- Finite words in the three generators. -/
abbrev pom_three_gen_termination_word := List pom_three_gen_termination_token

/-- Count how many letters in `w` are strictly smaller than `a`. -/
def pom_three_gen_termination_lowerCount
    (a : pom_three_gen_termination_token) : pom_three_gen_termination_word → ℕ
  | [] => 0
  | b :: w => (if b < a then 1 else 0) + pom_three_gen_termination_lowerCount a w

/-- Standard inversion count for the ordered alphabet `0 < 1 < 2`. -/
def pom_three_gen_termination_inversionCount : pom_three_gen_termination_word → ℕ
  | [] => 0
  | a :: w =>
      pom_three_gen_termination_lowerCount a w + pom_three_gen_termination_inversionCount w

/-- Lexicographic rank `(length, inversionCount)` used for termination. -/
def pom_three_gen_termination_rank :
    pom_three_gen_termination_word → Nat ×ₗ Nat
  | w => toLex (w.length, pom_three_gen_termination_inversionCount w)

/-- Predecessor-oriented rewrite relation: contractions strictly shorten the word, while commuting
steps preserve length and strictly lower the inversion count. -/
inductive pom_three_gen_termination_rewrite_step :
    pom_three_gen_termination_word → pom_three_gen_termination_word → Prop
  | contract {w' w : pom_three_gen_termination_word} (hlen : w'.length < w.length) :
      pom_three_gen_termination_rewrite_step w' w
  | commute {w' w : pom_three_gen_termination_word}
      (hlen : w'.length = w.length)
      (hinv : pom_three_gen_termination_inversionCount w' <
        pom_three_gen_termination_inversionCount w) :
      pom_three_gen_termination_rewrite_step w' w

lemma pom_three_gen_termination_step_rank
    {w' w : pom_three_gen_termination_word}
    (h : pom_three_gen_termination_rewrite_step w' w) :
    pom_three_gen_termination_rank w' < pom_three_gen_termination_rank w := by
  cases h with
  | contract hlen =>
      change toLex (w'.length, pom_three_gen_termination_inversionCount w') <
        toLex (w.length, pom_three_gen_termination_inversionCount w)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hlen
  | commute hlen hinv =>
      change toLex (w'.length, pom_three_gen_termination_inversionCount w') <
        toLex (w.length, pom_three_gen_termination_inversionCount w)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨hlen, hinv⟩

/-- Paper label: `prop:pom-three-gen-termination`. -/
theorem paper_pom_three_gen_termination :
    WellFounded pom_three_gen_termination_rewrite_step := by
  exact WellFounded.mono
    (InvImage.wf pom_three_gen_termination_rank wellFounded_lt)
    (fun _ _ h => pom_three_gen_termination_step_rank h)

end Omega.POM
