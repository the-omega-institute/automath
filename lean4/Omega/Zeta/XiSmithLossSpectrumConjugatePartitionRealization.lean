import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

lemma xi_smith_loss_spectrum_conjugate_partition_realization_sum_range_lt (m a : ℕ)
    (ha : a ≤ m) :
    (∑ i ∈ Finset.range m, if i < a then 1 else 0) = a := by
  induction m with
  | zero =>
      have : a = 0 := by omega
      subst a
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      by_cases ha' : a ≤ m
      · have hlast : (if m < a then 1 else 0) = 0 := by simp [not_lt.mpr ha']
        rw [hlast, add_zero]
        exact ih ha'
      · have haeq : a = m + 1 := by omega
        subst a
        have hsum : (∑ i ∈ Finset.range m, if i < m + 1 then 1 else 0) = m := by
          rw [← Finset.card_filter]
          have hfilter : (Finset.range m).filter (fun i => i < m + 1) = Finset.range m := by
            apply Finset.filter_true_of_mem
            intro i hi
            exact Nat.lt_succ_of_lt (Finset.mem_range.mp hi)
          rw [hfilter, Finset.card_range]
        rw [hsum]
        simp

lemma xi_smith_loss_spectrum_conjugate_partition_realization_sum_fin_lt (m a : ℕ)
    (ha : a ≤ m) :
    (∑ i : Fin m, if (i : ℕ) < a then 1 else 0) = a := by
  calc
    (∑ i : Fin m, if (i : ℕ) < a then 1 else 0) =
        ∑ i ∈ Finset.range m, if i < a then 1 else 0 := by
      simpa using (Fin.sum_univ_eq_sum_range (fun i => if i < a then (1 : ℕ) else 0) m)
    _ = a := xi_smith_loss_spectrum_conjugate_partition_realization_sum_range_lt m a ha

lemma xi_smith_loss_spectrum_conjugate_partition_realization_range_filter_lt_card
    (n k : ℕ) :
    ((Finset.range k).filter (fun r => r < n)).card = Nat.min n k := by
  rw [Finset.card_filter]
  have hcongr :
      (∑ r ∈ Finset.range k, if r < n then 1 else 0) =
        ∑ r ∈ Finset.range k, if r < Nat.min n k then 1 else 0 := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hrk : r < k := Finset.mem_range.mp hr
    by_cases hrn : r < n
    · have hmin : r < Nat.min n k := lt_min hrn hrk
      simp [hrn, hmin]
    · have hmin : ¬r < Nat.min n k := by
        intro h
        exact hrn (lt_of_lt_of_le h (Nat.min_le_left n k))
      simp [hrn, hmin]
  rw [hcongr]
  exact xi_smith_loss_spectrum_conjugate_partition_realization_sum_range_lt k
    (Nat.min n k) (Nat.min_le_right n k)

/-- Paper label: `thm:xi-smith-loss-spectrum-conjugate-partition-realization`. -/
theorem paper_xi_smith_loss_spectrum_conjugate_partition_realization {m : ℕ}
    (Δ : ℕ → ℕ) (hmono : ∀ k, Δ (k + 1) ≤ Δ k) (hbound : ∀ k, Δ k ≤ m)
    (hzero : ∃ K, ∀ k, K ≤ k → Δ k = 0) :
    ∃ e : Fin m → ℕ, (∀ i j : Fin m, (i : ℕ) ≤ j → e j ≤ e i) ∧
      ∀ k : ℕ, Omega.Zeta.smithPrefixValue e k = ∑ r ∈ Finset.range k, Δ (r + 1) := by
  classical
  have hmono_le : ∀ {a b : ℕ}, a ≤ b → Δ b ≤ Δ a := by
    intro a b hab
    induction hab with
    | refl => rfl
    | step h ih => exact le_trans (hmono _) ih
  let P : Fin m → ℕ → Prop := fun i n => ∀ r, n ≤ r → Δ (r + 1) ≤ (i : ℕ)
  have hP_ex : ∀ i : Fin m, ∃ n, P i n := by
    intro i
    rcases hzero with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro r hr
    rw [hK (r + 1) (le_trans hr (Nat.le_succ r))]
    exact Nat.zero_le _
  let e : Fin m → ℕ := fun i => Nat.find (hP_ex i)
  have htail : ∀ i r, e i ≤ r → Δ (r + 1) ≤ (i : ℕ) := by
    intro i
    exact Nat.find_spec (hP_ex i)
  have hhead : ∀ i r, r < e i → (i : ℕ) < Δ (r + 1) := by
    intro i r hr
    by_contra hnot
    have hle : Δ (r + 1) ≤ (i : ℕ) := Nat.le_of_not_gt hnot
    have hPr : P i r := by
      intro s hs
      exact le_trans (hmono_le (Nat.succ_le_succ hs)) hle
    have : e i ≤ r := Nat.find_min' (hP_ex i) hPr
    omega
  have hlevel : ∀ i : Fin m, ∀ r : ℕ, ((i : ℕ) < Δ (r + 1)) ↔ r < e i := by
    intro i r
    constructor
    · intro hlt
      by_contra hnlt
      have her : e i ≤ r := Nat.le_of_not_gt hnlt
      have hdle := htail i r her
      omega
    · exact hhead i r
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    have hPj : P j (e i) := by
      intro r hr
      exact le_trans (htail i r hr) hij
    exact Nat.find_min' (hP_ex j) hPj
  · intro k
    have hmin_count : ∀ i : Fin m,
        Nat.min (e i) k = ∑ r ∈ Finset.range k, if (i : ℕ) < Δ (r + 1) then 1 else 0 := by
      intro i
      calc
        Nat.min (e i) k = ((Finset.range k).filter (fun r => r < e i)).card := by
          rw [xi_smith_loss_spectrum_conjugate_partition_realization_range_filter_lt_card]
        _ = ((Finset.range k).filter (fun r => (i : ℕ) < Δ (r + 1))).card := by
          congr 1
          ext r
          simp [hlevel i r]
        _ = ∑ r ∈ Finset.range k, if (i : ℕ) < Δ (r + 1) then 1 else 0 := by
          rw [Finset.card_filter]
    calc
      Omega.Zeta.smithPrefixValue e k = ∑ i : Fin m, Nat.min (e i) k := by
        rfl
      _ = ∑ i : Fin m, ∑ r ∈ Finset.range k,
          if (i : ℕ) < Δ (r + 1) then 1 else 0 := by
        simp [hmin_count]
      _ = ∑ r ∈ Finset.range k, ∑ i : Fin m,
          if (i : ℕ) < Δ (r + 1) then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ r ∈ Finset.range k, Δ (r + 1) := by
        refine Finset.sum_congr rfl ?_
        intro r _
        exact xi_smith_loss_spectrum_conjugate_partition_realization_sum_fin_lt m
          (Δ (r + 1)) (hbound (r + 1))

end Omega.Zeta
