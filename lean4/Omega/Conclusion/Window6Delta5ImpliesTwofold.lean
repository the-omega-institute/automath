import Mathlib
import Mathlib.Data.Finset.SymmDiff

namespace Omega.Conclusion

open scoped symmDiff

/-- Concrete window-6 packing statement used in the `δ_min = 5` fiber analysis: every family of
subsets of the `6`-cube with pairwise Hamming distance at least `5` has cardinality `2` as soon as
it contains at least two points. -/
def conclusion_window6_delta5_implies_twofold_statement : Prop :=
  ∀ C : Finset (Finset (Fin 6)),
    2 ≤ C.card →
    (∀ s ∈ C, ∀ t ∈ C, s ≠ t → 5 ≤ (s ∆ t).card) →
    C.card = 2

private lemma conclusion_window6_delta5_implies_twofold_compl_card_le_one
    (s : Finset (Fin 6)) (hs : 5 ≤ s.card) : (Finset.univ \ s).card ≤ 1 := by
  have hcard :
      (Finset.univ \ s).card + s.card = Fintype.card (Fin 6) := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  have hfin : Fintype.card (Fin 6) = 6 := by simp
  omega

private lemma conclusion_window6_delta5_implies_twofold_symmDiff_subset_compl_union
    (s t : Finset (Fin 6)) : s ∆ t ⊆ (Finset.univ \ s) ∪ (Finset.univ \ t) := by
  intro i hi
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
  simp only [Finset.mem_symmDiff] at hi
  rcases hi with h | h <;> simp [h.2]

private lemma conclusion_window6_delta5_implies_twofold_symmDiff_card_le_two
    (s t : Finset (Fin 6)) (hs : 5 ≤ s.card) (ht : 5 ≤ t.card) : (s ∆ t).card ≤ 2 := by
  have hs' := conclusion_window6_delta5_implies_twofold_compl_card_le_one s hs
  have ht' := conclusion_window6_delta5_implies_twofold_compl_card_le_one t ht
  calc
    (s ∆ t).card ≤ ((Finset.univ \ s) ∪ (Finset.univ \ t)).card := by
      exact Finset.card_le_card
        (conclusion_window6_delta5_implies_twofold_symmDiff_subset_compl_union s t)
    _ ≤ (Finset.univ \ s).card + (Finset.univ \ t).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := by omega
    _ = 2 := by norm_num

private lemma conclusion_window6_delta5_implies_twofold_translate_symmDiff
    (a b c : Finset (Fin 6)) : (a ∆ b) ∆ (a ∆ c) = b ∆ c := by
  calc
    (a ∆ b) ∆ (a ∆ c) = b ∆ (a ∆ (a ∆ c)) := by
      rw [symmDiff_comm a b, symmDiff_assoc]
    _ = b ∆ c := by rw [symmDiff_symmDiff_cancel_left]

/-- Paper label: `prop:conclusion-window6-delta5-implies-twofold`. In the `6`-cube, three points
cannot be pairwise Hamming-distance at least `5`; therefore every such family with at least two
points has exactly two points. -/
theorem paper_conclusion_window6_delta5_implies_twofold :
    conclusion_window6_delta5_implies_twofold_statement := by
  intro C hC_two hpair
  have hC_le_two : C.card ≤ 2 := by
    by_contra hC_not_le_two
    have hC_three : 2 < C.card := by omega
    rcases (Finset.two_lt_card.mp hC_three) with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
    have hab5 : 5 ≤ (a ∆ b).card := hpair a ha b hb hab
    have hac5 : 5 ≤ (a ∆ c).card := hpair a ha c hc hac
    have hbc5 : 5 ≤ (b ∆ c).card := hpair b hb c hc hbc
    have hsmall :
        ((a ∆ b) ∆ (a ∆ c)).card ≤ 2 :=
      conclusion_window6_delta5_implies_twofold_symmDiff_card_le_two (a ∆ b) (a ∆ c) hab5 hac5
    have hsmall' : (b ∆ c).card ≤ 2 := by
      simpa [conclusion_window6_delta5_implies_twofold_translate_symmDiff a b c] using hsmall
    omega
  exact le_antisymm hC_le_two hC_two

end Omega.Conclusion
