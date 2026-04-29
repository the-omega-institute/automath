import Omega.Combinatorics.PathIndSet

namespace Omega.Zeta

/-- A concrete tail word is represented by the set of positions carrying a `1`. -/
def xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_word
    (L : ℕ) (S : Finset (Fin L)) : Prop :=
  Omega.IsPathIndependent L S

/-- The last-bit strengthening forces the first tail coordinate to be zero. -/
def xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_condition
    (L : ℕ) (S : Finset (Fin L)) : Prop :=
  ∀ h : 0 < L, (⟨0, h⟩ : Fin L) ∉ S

/-- Feasible tails are no-adjacent-one tails satisfying the finite threshold audit. -/
def xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_feasible_tail
    (L budget : ℕ) (S : Finset (Fin L)) : Prop :=
  xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_word L S ∧
    S.card ≤ budget

instance xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_feasible_tail_decidable
    (L budget : ℕ) :
    DecidablePred
      (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_feasible_tail L budget) := by
  intro S
  unfold xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_feasible_tail
    xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_word
  infer_instance

/-- The finite family of feasible tails before using the last visible bit. -/
def xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words
    (L budget : ℕ) : Finset (Finset (Fin L)) :=
  Finset.univ.filter
    (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_feasible_tail L budget)

/-- After the last-bit condition the first tail bit is fixed to zero, leaving `L - 1` sites. -/
def xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_tail_words
    (L budget : ℕ) : Finset (Finset (Fin (L - 1))) :=
  xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words (L - 1) budget

def xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_statement : Prop :=
  ∀ L budget : ℕ,
    (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words L budget).card ≤
        Nat.fib (L + 2) ∧
      (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_tail_words
          L budget).card ≤
        Nat.fib (L + 1)

lemma xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words_card_le
    (L budget : ℕ) :
    (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words L budget).card ≤
      Nat.fib (L + 2) := by
  calc
    (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words L budget).card ≤
        (Finset.univ.filter fun S : Finset (Fin L) => Omega.IsPathIndependent L S).card := by
          apply Finset.card_le_card
          intro S hS
          have hS' := (Finset.mem_filter.mp hS).2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ S,
              hS'.1⟩
    _ = Nat.fib (L + 2) := Omega.path_independent_set_count' L

lemma xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_card_le
    (L budget : ℕ) :
    (xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_tail_words
        L budget).card ≤
      Nat.fib (L + 1) := by
  have h :=
    xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words_card_le
      (L - 1) budget
  cases L with
  | zero =>
      simpa [xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_tail_words,
        Nat.fib] using h
  | succ L =>
      simpa [xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_tail_words]
        using h

/-- Paper label: `thm:xi-foldbin-universal-fibonacci-upper-bound-lastbit-improvement`. -/
theorem paper_xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement :
    xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_statement := by
  intro L budget
  exact
    ⟨xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_tail_words_card_le L budget,
      xi_foldbin_universal_fibonacci_upper_bound_lastbit_improvement_lastbit_card_le L budget⟩

end Omega.Zeta
