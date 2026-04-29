import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the zero-slack screen criterion over a finite ground screen. -/
structure conclusion_screen_zero_slack_matroid_basis_criterion_data where
  Point : Type*
  ground : Finset Point
  rank : Finset Point → ℕ
  totalRank : ℕ
  independent : Finset Point → Prop
  basis : Finset Point → Prop
  greedy : ℕ → Finset Point
  greedy_subset_ground : ∀ n, greedy n ⊆ ground
  rank_le_card : ∀ S : Finset Point, rank S ≤ S.card
  independent_iff_rank_card : ∀ S : Finset Point, independent S ↔ rank S = S.card
  basis_of_full_independent :
    ∀ S : Finset Point, rank S = totalRank → independent S → basis S
  greedy_rank_zero : rank (greedy 0) = 0
  greedy_rank_step :
    ∀ n : ℕ, n < totalRank → rank (greedy (n + 1)) = rank (greedy n) + 1
  greedy_card_full : (greedy totalRank).card = totalRank

/-- The matroid slack of a screen. -/
def conclusion_screen_zero_slack_matroid_basis_criterion_slack
    (D : conclusion_screen_zero_slack_matroid_basis_criterion_data)
    (S : Finset D.Point) : ℕ :=
  S.card - D.rank S

/-- Zero slack is exactly independence. -/
def conclusion_screen_zero_slack_matroid_basis_criterion_data.zero_slack_law
    (D : conclusion_screen_zero_slack_matroid_basis_criterion_data) : Prop :=
  ∀ S : Finset D.Point,
    conclusion_screen_zero_slack_matroid_basis_criterion_slack D S = 0 ↔ D.independent S

/-- A full-rank zero-slack screen is a basis. -/
def conclusion_screen_zero_slack_matroid_basis_criterion_data.minimal_exact_screens_are_bases
    (D : conclusion_screen_zero_slack_matroid_basis_criterion_data) : Prop :=
  ∀ S : Finset D.Point,
    D.rank S = D.totalRank →
      conclusion_screen_zero_slack_matroid_basis_criterion_slack D S = 0 →
        D.basis S

/-- The greedy trajectory reaches a basis at the full-rank time. -/
def conclusion_screen_zero_slack_matroid_basis_criterion_data.greedy_terminates_with_basis
    (D : conclusion_screen_zero_slack_matroid_basis_criterion_data) : Prop :=
  D.basis (D.greedy D.totalRank)

lemma conclusion_screen_zero_slack_matroid_basis_criterion_greedy_rank
    (D : conclusion_screen_zero_slack_matroid_basis_criterion_data) :
    ∀ n : ℕ, n ≤ D.totalRank → D.rank (D.greedy n) = n := by
  intro n hn
  induction n with
  | zero =>
      exact D.greedy_rank_zero
  | succ n ih =>
      have hn_lt : n < D.totalRank := Nat.succ_le_iff.mp hn
      rw [D.greedy_rank_step n hn_lt, ih (Nat.le_of_lt hn_lt)]

/-- Paper label: `thm:conclusion-screen-zero-slack-matroid-basis-criterion`. -/
theorem paper_conclusion_screen_zero_slack_matroid_basis_criterion
    (D : conclusion_screen_zero_slack_matroid_basis_criterion_data) :
    D.zero_slack_law ∧ D.minimal_exact_screens_are_bases ∧
      D.greedy_terminates_with_basis := by
  have hzero : D.zero_slack_law := by
    intro S
    constructor
    · intro hslack
      rw [conclusion_screen_zero_slack_matroid_basis_criterion_slack,
        Nat.sub_eq_zero_iff_le] at hslack
      exact (D.independent_iff_rank_card S).2 (Nat.le_antisymm (D.rank_le_card S) hslack)
    · intro hind
      rw [conclusion_screen_zero_slack_matroid_basis_criterion_slack]
      exact Nat.sub_eq_zero_of_le (le_of_eq ((D.independent_iff_rank_card S).1 hind).symm)
  have hminimal : D.minimal_exact_screens_are_bases := by
    intro S hfull hslack
    exact D.basis_of_full_independent S hfull ((hzero S).1 hslack)
  have hgreedy : D.greedy_terminates_with_basis := by
    have hfullrank : D.rank (D.greedy D.totalRank) = D.totalRank :=
      conclusion_screen_zero_slack_matroid_basis_criterion_greedy_rank D D.totalRank le_rfl
    have hind : D.independent (D.greedy D.totalRank) := by
      refine (D.independent_iff_rank_card (D.greedy D.totalRank)).2 ?_
      rw [hfullrank, D.greedy_card_full]
    exact D.basis_of_full_independent (D.greedy D.totalRank) hfullrank hind
  exact ⟨hzero, hminimal, hgreedy⟩

end Omega.Conclusion
