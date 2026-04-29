import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The `k`th column height of a finite Smith valuation profile. Levels are zero-based, so
`k < e i` means that row `i` reaches level `k + 1`. -/
def conclusion_smith_loss_profile_young_duality_column_height
    {m : ℕ} (e : Fin m → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => k < e i)).card

/-- Sum of the first `ell` row lengths of a finite Smith valuation profile. -/
def conclusion_smith_loss_profile_young_duality_row_prefix
    {m : ℕ} (e : Fin m → ℕ) (ell : ℕ) : ℕ :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin m => i.val < ell)), e i

/-- The Ferrers-dual column count restricted to the first `ell` rows. -/
def conclusion_smith_loss_profile_young_duality_column_prefix
    {m : ℕ} (e : Fin m → ℕ) (ell k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => i.val < ell ∧ k < e i)).card

/-- Concrete finite Young-duality statement for nonincreasing Smith valuation profiles. -/
def conclusion_smith_loss_profile_young_duality_statement : Prop :=
  ∀ (m H : ℕ) (e : Fin m → ℕ),
    (∀ i : Fin m, e i ≤ H) →
    (∀ i j : Fin m, i.val ≤ j.val → e j ≤ e i) →
      (∀ j : Fin m,
        e j =
          ((Finset.range H).filter (fun k =>
            j.val < conclusion_smith_loss_profile_young_duality_column_height e k)).card) ∧
      ∀ ell : ℕ, ell ≤ m →
        conclusion_smith_loss_profile_young_duality_row_prefix e ell =
          ∑ k ∈ Finset.range H,
            min ell (conclusion_smith_loss_profile_young_duality_column_height e k)

lemma conclusion_smith_loss_profile_young_duality_row_length
    {m H : ℕ} (e : Fin m → ℕ) (hH : ∀ i : Fin m, e i ≤ H)
    (hmono : ∀ i j : Fin m, i.val ≤ j.val → e j ≤ e i) (j : Fin m) :
    e j =
      ((Finset.range H).filter (fun k =>
        j.val < conclusion_smith_loss_profile_young_duality_column_height e k)).card := by
  have hset :
      (Finset.range H).filter
          (fun k => j.val < conclusion_smith_loss_profile_young_duality_column_height e k) =
        (Finset.range H).filter (fun k => k < e j) := by
    ext k
    by_cases hkH : k < H
    · have hp :
          (∀ i l : Fin m, l ≤ i → k < e i → k < e l) := by
        intro i l hli hki
        exact lt_of_lt_of_le hki (hmono l i hli)
      have hiff :
          j.val < conclusion_smith_loss_profile_young_duality_column_height e k ↔ k < e j := by
        simpa [conclusion_smith_loss_profile_young_duality_column_height] using
          (Fin.lt_card_filter_univ_iff_apply_of_imp (n := m)
            (j := j) (p := fun i : Fin m => k < e i) hp)
      simp [hkH, hiff]
    · have hnot : ¬k < e j := fun hkj => hkH (lt_of_lt_of_le hkj (hH j))
      simp [hkH, hnot]
  rw [hset]
  have hfilter :
      (Finset.range H).filter (fun k => k < e j) = Finset.range (e j) := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hk => hk.2,
      fun hk => ⟨lt_of_lt_of_le hk (hH j), hk⟩⟩
  simp [hfilter]

lemma conclusion_smith_loss_profile_young_duality_column_prefix_eq_min
    {m : ℕ} (e : Fin m → ℕ)
    (hmono : ∀ i j : Fin m, i.val ≤ j.val → e j ≤ e i) {ell : ℕ} (hell : ell ≤ m)
    (k : ℕ) :
    conclusion_smith_loss_profile_young_duality_column_prefix e ell k =
      min ell (conclusion_smith_loss_profile_young_duality_column_height e k) := by
  have hp : ∀ i l : Fin m, l ≤ i → k < e i → k < e l := by
    intro i l hli hki
    exact lt_of_lt_of_le hki (hmono l i hli)
  have hset :
      (Finset.univ.filter (fun i : Fin m => i.val < ell ∧ k < e i)) =
        (Finset.univ.filter (fun i : Fin m =>
          i.val < min ell (conclusion_smith_loss_profile_young_duality_column_height e k))) := by
    ext i
    have hiff :
        i.val < conclusion_smith_loss_profile_young_duality_column_height e k ↔ k < e i := by
      simpa [conclusion_smith_loss_profile_young_duality_column_height] using
        (Fin.lt_card_filter_univ_iff_apply_of_imp (n := m)
          (j := i) (p := fun i : Fin m => k < e i) hp)
    simp [hiff]
  rw [conclusion_smith_loss_profile_young_duality_column_prefix, hset]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right ((Nat.min_le_left ell _).trans hell)

/-- Paper label: `cor:conclusion-smith-loss-profile-young-duality`. -/
theorem paper_conclusion_smith_loss_profile_young_duality :
    conclusion_smith_loss_profile_young_duality_statement := by
  intro m H e hH hmono
  refine ⟨?_, ?_⟩
  · intro j
    exact conclusion_smith_loss_profile_young_duality_row_length e hH hmono j
  · intro ell hell
    unfold conclusion_smith_loss_profile_young_duality_row_prefix
    calc
      (∑ i ∈ (Finset.univ.filter (fun i : Fin m => i.val < ell)), e i)
          =
          ∑ i ∈ (Finset.univ.filter (fun i : Fin m => i.val < ell)),
            ((Finset.range H).filter (fun k => k < e i)).card := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            have hfilter :
                (Finset.range H).filter (fun k => k < e i) = Finset.range (e i) := by
              apply Finset.ext
              intro k
              simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨fun hk => hk.2,
                fun hk => ⟨lt_of_lt_of_le hk (hH i), hk⟩⟩
            simp [hfilter]
      _ =
          ∑ k ∈ Finset.range H,
            conclusion_smith_loss_profile_young_duality_column_prefix e ell k := by
            simp only [conclusion_smith_loss_profile_young_duality_column_prefix,
              Finset.card_eq_sum_ones, Finset.sum_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            by_cases hi : i.val < ell
            · simp [hi]
            · simp [hi]
      _ =
          ∑ k ∈ Finset.range H,
            min ell (conclusion_smith_loss_profile_young_duality_column_height e k) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            exact conclusion_smith_loss_profile_young_duality_column_prefix_eq_min e hmono hell k

end Omega.Conclusion
