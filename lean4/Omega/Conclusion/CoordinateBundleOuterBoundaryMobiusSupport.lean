import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

private lemma conclusion_coordinate_bundle_outer_boundary_mobius_support_total
    {α : Type*} [DecidableEq α] (S : Finset α) :
    (∑ U ∈ S.powerset, (-1 : ℤ) ^ (S.card - U.card)) =
      if S = ∅ then (1 : ℤ) else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a S ha ih =>
      rw [Finset.powerset_insert]
      have hdisj : Disjoint (S.powerset.image (insert a)) S.powerset := by
        rw [Finset.disjoint_left]
        intro U hUimage hUpow
        rcases Finset.mem_image.mp hUimage with ⟨V, _hVpow, rfl⟩
        exact ha ((Finset.mem_powerset.mp hUpow) (Finset.mem_insert_self a V))
      rw [Finset.sum_union hdisj.symm]
      rw [Finset.sum_image]
      · simp only [Finset.card_insert_of_notMem ha]
        rw [show
            (∑ x ∈ S.powerset, (-1 : ℤ) ^ (S.card + 1 - (insert a x).card)) =
              ∑ x ∈ S.powerset, (-1 : ℤ) ^ (S.card - x.card) by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUS : U ⊆ S := Finset.mem_powerset.mp hU
          have hnot : a ∉ U := fun h => ha (hUS h)
          simp [Finset.card_insert_of_notMem hnot]]
        rw [show
            (∑ x ∈ S.powerset, (-1 : ℤ) ^ (S.card + 1 - x.card)) =
              -∑ x ∈ S.powerset, (-1 : ℤ) ^ (S.card - x.card) by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUS : U ⊆ S := Finset.mem_powerset.mp hU
          have hle : U.card ≤ S.card := Finset.card_le_card hUS
          have hsucc : S.card + 1 - U.card = (S.card - U.card) + 1 := by
            omega
          rw [hsucc, pow_succ]
          ring]
        simp
      · intro U hU V hV hEq
        ext x
        constructor
        · intro hxU
          have hx : x ∈ insert a V := by
            rw [← hEq]
            exact Finset.mem_insert_of_mem hxU
          rcases Finset.mem_insert.mp hx with rfl | hxV
          · exact False.elim (ha ((Finset.mem_powerset.mp hU) hxU))
          · exact hxV
        · intro hxV
          have hx : x ∈ insert a U := by
            rw [hEq]
            exact Finset.mem_insert_of_mem hxV
          rcases Finset.mem_insert.mp hx with rfl | hxU
          · exact False.elim (ha ((Finset.mem_powerset.mp hV) hxV))
          · exact hxU

private lemma conclusion_coordinate_bundle_outer_boundary_mobius_support_single_layer
    {α : Type*} [DecidableEq α] (S T : Finset α)
    [∀ U : Finset α, Decidable ((U ∩ T).Nonempty)] :
    (∑ U ∈ S.powerset,
        (-1 : ℤ) ^ (S.card - U.card) * if (U ∩ T).Nonempty then (1 : ℤ) else 0) =
      if S.Nonempty ∧ S ⊆ T then (-1 : ℤ) ^ (S.card + 1) else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a S ha ih =>
      by_cases haT : a ∈ T
      · rw [Finset.powerset_insert]
        have hdisj :
            Disjoint (S.powerset.image (insert a)) S.powerset := by
          rw [Finset.disjoint_left]
          intro U hUimage hUpow
          rcases Finset.mem_image.mp hUimage with ⟨V, _hVpow, rfl⟩
          exact ha ((Finset.mem_powerset.mp hUpow) (Finset.mem_insert_self a V))
        rw [Finset.sum_union hdisj.symm]
        rw [Finset.sum_image]
        · have hsum :
              (∑ U ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card - U.card) * if (U ∩ T).Nonempty then (1 : ℤ) else 0) =
                if S.Nonempty ∧ S ⊆ T then (-1 : ℤ) ^ (S.card + 1) else 0 := ih
          have htotal :
              (∑ U ∈ S.powerset, (-1 : ℤ) ^ (S.card - U.card)) =
                if S = ∅ then (1 : ℤ) else 0 := by
            exact conclusion_coordinate_bundle_outer_boundary_mobius_support_total S
          simp only [Finset.card_insert_of_notMem ha]
          rw [show
              (∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card + 1 - (insert a x).card) *
                    (if (insert a x ∩ T).Nonempty then (1 : ℤ) else 0)) =
                ∑ x ∈ S.powerset, (-1 : ℤ) ^ (S.card - x.card) by
            refine Finset.sum_congr rfl ?_
            intro U hU
            have hUS : U ⊆ S := Finset.mem_powerset.mp hU
            have hnot : a ∉ U := fun h => ha (hUS h)
            have hnon : (insert a U ∩ T).Nonempty := ⟨a, by simp [haT]⟩
            simp [Finset.card_insert_of_notMem hnot, hnon]]
          rw [show
              (∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card + 1 - x.card) *
                    (if (x ∩ T).Nonempty then (1 : ℤ) else 0)) =
                -∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card - x.card) *
                    (if (x ∩ T).Nonempty then (1 : ℤ) else 0) by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro U hU
            have hUS : U ⊆ S := Finset.mem_powerset.mp hU
            have hle : U.card ≤ S.card := Finset.card_le_card hUS
            have hsucc : S.card + 1 - U.card = (S.card - U.card) + 1 := by
              omega
            rw [hsucc, pow_succ]
            ring]
          by_cases hS : S = ∅
          · subst hS
            simp [haT]
          · have hSnon : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
            by_cases hsub : S ⊆ T
            · have hinsert : (insert a S).Nonempty ∧ insert a S ⊆ T := by
                constructor
                · exact ⟨a, Finset.mem_insert_self a S⟩
                · intro x hx
                  rcases Finset.mem_insert.mp hx with rfl | hxS
                  · exact haT
                  · exact hsub hxS
              rw [htotal, if_neg hS, hsum, if_pos ⟨hSnon, hsub⟩, if_pos hinsert]
              rw [pow_succ]
              ring
            · have hinsert_not : ¬((insert a S).Nonempty ∧ insert a S ⊆ T) := by
                intro h
                exact hsub (fun x hx => h.2 (Finset.mem_insert_of_mem hx))
              rw [htotal, if_neg hS, hsum, if_neg (by exact fun h => hsub h.2),
                if_neg hinsert_not]
              ring
        · intro U hU V _hV hEq
          ext x
          constructor
          · intro hxU
            have hx : x ∈ insert a V := by
              rw [← hEq]
              exact Finset.mem_insert_of_mem hxU
            rcases Finset.mem_insert.mp hx with rfl | hxV
            · exact False.elim (ha ((Finset.mem_powerset.mp hU) hxU))
            · exact hxV
          · intro hxV
            have hx : x ∈ insert a U := by
              rw [hEq]
              exact Finset.mem_insert_of_mem hxV
            rcases Finset.mem_insert.mp hx with rfl | hxU
            · exact False.elim (ha ((Finset.mem_powerset.mp _hV) hxV))
            · exact hxU
      · rw [Finset.powerset_insert]
        have hdisj :
            Disjoint (S.powerset.image (insert a)) S.powerset := by
          rw [Finset.disjoint_left]
          intro U hUimage hUpow
          rcases Finset.mem_image.mp hUimage with ⟨V, _hVpow, rfl⟩
          exact ha ((Finset.mem_powerset.mp hUpow) (Finset.mem_insert_self a V))
        rw [Finset.sum_union hdisj.symm]
        rw [Finset.sum_image]
        · simp only [Finset.card_insert_of_notMem ha]
          rw [show
              (∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card + 1 - (insert a x).card) *
                    (if (insert a x ∩ T).Nonempty then (1 : ℤ) else 0)) =
                ∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card - x.card) *
                    (if (x ∩ T).Nonempty then (1 : ℤ) else 0) by
            refine Finset.sum_congr rfl ?_
            intro U hU
            have hUS : U ⊆ S := Finset.mem_powerset.mp hU
            have hnot : a ∉ U := fun h => ha (hUS h)
            have hinter : (insert a U ∩ T).Nonempty ↔ (U ∩ T).Nonempty := by
              constructor
              · rintro ⟨x, hx⟩
                have hxmem := Finset.mem_inter.mp hx
                rcases Finset.mem_insert.mp hxmem.1 with rfl | hxU
                · exact False.elim (haT hxmem.2)
                · exact ⟨x, by simp [hxU, hxmem.2]⟩
              · rintro ⟨x, hx⟩
                have hxmem := Finset.mem_inter.mp hx
                exact ⟨x, by simp [hxmem.1, hxmem.2]⟩
            simp [Finset.card_insert_of_notMem hnot, hinter]]
          rw [show
              (∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card + 1 - x.card) *
                    (if (x ∩ T).Nonempty then (1 : ℤ) else 0)) =
                -∑ x ∈ S.powerset,
                  (-1 : ℤ) ^ (S.card - x.card) *
                    (if (x ∩ T).Nonempty then (1 : ℤ) else 0) by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro U hU
            have hUS : U ⊆ S := Finset.mem_powerset.mp hU
            have hle : U.card ≤ S.card := Finset.card_le_card hUS
            have hsucc : S.card + 1 - U.card = (S.card - U.card) + 1 := by
              omega
            rw [hsucc, pow_succ]
            ring]
          have hinsert_not : ¬((insert a S).Nonempty ∧ insert a S ⊆ T) := by
            intro h
            exact haT (h.2 (Finset.mem_insert_self a S))
          rw [if_neg hinsert_not]
          ring
        · intro U hU V _hV hEq
          ext x
          constructor
          · intro hxU
            have hx : x ∈ insert a V := by
              rw [← hEq]
              exact Finset.mem_insert_of_mem hxU
            rcases Finset.mem_insert.mp hx with rfl | hxV
            · exact False.elim (ha ((Finset.mem_powerset.mp hU) hxU))
            · exact hxV
          · intro hxV
            have hx : x ∈ insert a U := by
              rw [hEq]
              exact Finset.mem_insert_of_mem hxV
            rcases Finset.mem_insert.mp hx with rfl | hxU
            · exact False.elim (ha ((Finset.mem_powerset.mp _hV) hxV))
            · exact hxU

private lemma conclusion_coordinate_bundle_outer_boundary_mobius_support_layer_sum
    {α ι : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (E : ι → Finset α) (S : Finset α)
    [∀ (B : Finset α) (i : ι), Decidable ((B ∩ E i).Nonempty)] :
    (∑ U ∈ S.powerset,
        (-1 : ℤ) ^ (S.card - U.card) *
          ((Finset.univ.filter (fun i : ι => (U ∩ E i).Nonempty)).card : ℤ)) =
      ∑ i : ι,
        if S.Nonempty ∧ S ⊆ E i then (-1 : ℤ) ^ (S.card + 1) else 0 := by
  classical
  calc
    (∑ U ∈ S.powerset,
        (-1 : ℤ) ^ (S.card - U.card) *
          ((Finset.univ.filter (fun i : ι => (U ∩ E i).Nonempty)).card : ℤ))
        =
      ∑ U ∈ S.powerset,
        (-1 : ℤ) ^ (S.card - U.card) *
          ∑ i : ι, if (U ∩ E i).Nonempty then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro U _hU
        congr 1
        rw [← Finset.sum_filter]
        simp
    _ =
      ∑ i : ι, ∑ U ∈ S.powerset,
        (-1 : ℤ) ^ (S.card - U.card) *
          if (U ∩ E i).Nonempty then (1 : ℤ) else 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ =
      ∑ i : ι,
        if S.Nonempty ∧ S ⊆ E i then (-1 : ℤ) ^ (S.card + 1) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact conclusion_coordinate_bundle_outer_boundary_mobius_support_single_layer S (E i)

/-- Paper label: `thm:conclusion-coordinate-bundle-outer-boundary-mobius-support`. -/
theorem paper_conclusion_coordinate_bundle_outer_boundary_mobius_support
    {α ι : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι] (E : ι → Finset α)
    (S : Finset α) [∀ (B : Finset α) (i : ι), Decidable ((B ∩ E i).Nonempty)]
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) :
    let g : Finset α → ℤ :=
      fun B => ((Finset.univ.filter (fun i : ι => (B ∩ E i).Nonempty)).card : ℤ)
    let mobius : ℤ := ∑ U ∈ S.powerset, (-1 : ℤ) ^ (S.card - U.card) * g U
    ((∃ i : ι, S.Nonempty ∧ S ⊆ E i) → mobius = (-1 : ℤ) ^ (S.card + 1)) ∧
      ((¬ ∃ i : ι, S.Nonempty ∧ S ⊆ E i) → mobius = 0) := by
  classical
  dsimp
  rw [conclusion_coordinate_bundle_outer_boundary_mobius_support_layer_sum E S]
  constructor
  · rintro ⟨i, hi⟩
    have hunique : ∀ j : ι, S.Nonempty ∧ S ⊆ E j ↔ j = i := by
      intro j
      constructor
      · intro hj
        by_contra hji
        rcases hi.1 with ⟨x, hxS⟩
        have hxi : x ∈ E i := hi.2 hxS
        have hxj : x ∈ E j := hj.2 hxS
        have hdisj' := hdisj j i hji
        rw [Finset.disjoint_left] at hdisj'
        exact hdisj' hxj hxi
      · intro hji
        subst hji
        exact hi
    rw [show
        (∑ j : ι,
            if S.Nonempty ∧ S ⊆ E j then (-1 : ℤ) ^ (S.card + 1) else 0) =
          ∑ j : ι, if j = i then (-1 : ℤ) ^ (S.card + 1) else 0 by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases h : S.Nonempty ∧ S ⊆ E j
      · have hji : j = i := (hunique j).mp h
        subst hji
        simp [hi]
      · have hji : j ≠ i := fun hji => h ((hunique j).mpr hji)
        simp [h, hji]]
    simp
  · intro hnone
    rw [show
        (∑ i : ι,
            if S.Nonempty ∧ S ⊆ E i then (-1 : ℤ) ^ (S.card + 1) else 0) =
          ∑ _i : ι, (0 : ℤ) by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hnot : ¬(S.Nonempty ∧ S ⊆ E i) := by
        intro hi
        exact hnone ⟨i, hi⟩
      simp [hnot]]
    simp

end Omega.Conclusion
