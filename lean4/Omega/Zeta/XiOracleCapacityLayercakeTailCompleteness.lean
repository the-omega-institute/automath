import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_oracle_capacity_layercake_tail_completeness_min_eq_sum_indicator
    (n T : ℕ) :
    Nat.min n T = ∑ k ∈ Finset.Icc 1 T, if k ≤ n then 1 else 0 := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      by_cases hT : T < n
      · have hmin_succ : Nat.min n (T + 1) = T + 1 :=
          Nat.min_eq_right (Nat.succ_le_of_lt hT)
        have hmin : Nat.min n T = T := Nat.min_eq_right (Nat.le_of_lt hT)
        rw [hmin_succ, Finset.sum_Icc_succ_top (by omega), ← ih, hmin]
        simp [Nat.succ_le_of_lt hT]
      · have hnT : n ≤ T := Nat.le_of_not_gt hT
        have hmin_succ : Nat.min n (T + 1) = n :=
          Nat.min_eq_left (Nat.le_trans hnT (Nat.le_succ T))
        have hmin : Nat.min n T = n := Nat.min_eq_left hnT
        have hnot : ¬T + 1 ≤ n := by omega
        rw [hmin_succ, Finset.sum_Icc_succ_top (by omega), ← ih, hmin]
        simp [hnot]

private lemma xi_oracle_capacity_layercake_tail_completeness_min_succ
    (n k : ℕ) (hk : 1 ≤ k) :
    Nat.min n k = Nat.min n (k - 1) + if k ≤ n then 1 else 0 := by
  by_cases hkn : k ≤ n
  · have hpred : k - 1 ≤ n := le_trans (Nat.sub_le k 1) hkn
    rw [show n.min k = k by exact Nat.min_eq_right hkn,
      show n.min (k - 1) = k - 1 by exact Nat.min_eq_right hpred, if_pos hkn]
    omega
  · have hnk : n ≤ k - 1 := by omega
    have hnk' : n ≤ k := by omega
    rw [show n.min k = n by exact Nat.min_eq_left hnk',
      show n.min (k - 1) = n by exact Nat.min_eq_left hnk, if_neg hkn]
    simp

private lemma xi_oracle_capacity_layercake_tail_completeness_tail_card_mono
    (d : Multiset ℕ) (k : ℕ) :
    (d.filter fun n => k + 1 ≤ n).card ≤ (d.filter fun n => k ≤ n).card := by
  induction d using Multiset.induction_on with
  | empty =>
      simp
  | cons a d ih =>
      rw [Multiset.filter_cons, Multiset.filter_cons]
      by_cases hsak : k + 1 ≤ a
      · have hak : k ≤ a := by omega
        simp [hsak, hak]
        simpa [Nat.succ_le_iff] using ih
      · by_cases hak : k ≤ a
        · simp [hsak, hak]
          exact le_trans (by simpa [Nat.succ_le_iff] using ih) (Nat.le_succ _)
        · simp [hsak, hak]
          simpa [Nat.succ_le_iff] using ih

private lemma xi_oracle_capacity_layercake_tail_completeness_capacity_step
    (d : Multiset ℕ) (k : ℕ) (hk : 1 ≤ k) :
    (d.map fun n => Nat.min n k).sum =
      (d.map fun n => Nat.min n (k - 1)).sum + (d.filter fun n => k ≤ n).card := by
  induction d using Multiset.induction_on with
  | empty =>
      simp
  | cons a d ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
      rw [Multiset.filter_cons]
      rw [xi_oracle_capacity_layercake_tail_completeness_min_succ a k hk, ih]
      by_cases hak : k ≤ a
      · simp [hak, add_assoc, add_comm, add_left_comm]
      · simp [hak, add_assoc, add_comm, add_left_comm]

private lemma xi_oracle_capacity_layercake_tail_completeness_count_eq_tail_sub_tail
    (d : Multiset ℕ) (k : ℕ) :
    d.count k = (d.filter fun n => k ≤ n).card - (d.filter fun n => k + 1 ≤ n).card := by
  induction d using Multiset.induction_on with
  | empty =>
      simp
  | cons a d ih =>
      rw [Multiset.count_cons, Multiset.filter_cons, Multiset.filter_cons]
      have hmono :=
        xi_oracle_capacity_layercake_tail_completeness_tail_card_mono d k
      have hmono' :
          (d.filter fun x => k < x).card ≤ (d.filter fun n => k ≤ n).card := by
        simpa [Nat.succ_le_iff] using hmono
      by_cases hak : k ≤ a
      · by_cases hsak : k + 1 ≤ a
        · have hak_ne : ¬k = a := by omega
          simp [hak, hsak, hak_ne, Nat.succ_le_iff, ih]
        · have haeq : a = k := by omega
          simp [hak, hsak, haeq, Nat.succ_le_iff, ih]
          omega
      · have hsak : ¬k + 1 ≤ a := by omega
        have hak_ne : ¬k = a := by omega
        simp [hak, hsak, hak_ne, Nat.succ_le_iff, ih]

/-- Paper label: `thm:xi-oracle-capacity-layercake-tail-completeness`. -/
theorem paper_xi_oracle_capacity_layercake_tail_completeness (d : Multiset ℕ) :
    (∀ T : ℕ,
      (d.map fun n => Nat.min n T).sum =
        ∑ k ∈ Finset.Icc 1 T, (d.filter fun n => k ≤ n).card) ∧
      (∀ k : ℕ, 1 ≤ k →
        (d.filter fun n => k ≤ n).card =
          (d.map fun n => Nat.min n k).sum -
            (d.map fun n => Nat.min n (k - 1)).sum) ∧
      (∀ k : ℕ, 1 ≤ k →
        d.count k =
          (d.filter fun n => k ≤ n).card - (d.filter fun n => k + 1 ≤ n).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T
    induction d using Multiset.induction_on with
    | empty =>
        simp
    | cons a d ih =>
        rw [Multiset.map_cons, Multiset.sum_cons, ih]
        calc
          Nat.min a T + ∑ k ∈ Finset.Icc 1 T, (d.filter fun n => k ≤ n).card =
              (∑ k ∈ Finset.Icc 1 T, if k ≤ a then 1 else 0) +
                ∑ k ∈ Finset.Icc 1 T, (d.filter fun n => k ≤ n).card := by
                rw [xi_oracle_capacity_layercake_tail_completeness_min_eq_sum_indicator]
          _ = ∑ k ∈ Finset.Icc 1 T,
                ((if k ≤ a then 1 else 0) + (d.filter fun n => k ≤ n).card) := by
                rw [Finset.sum_add_distrib]
          _ = ∑ k ∈ Finset.Icc 1 T, ((a ::ₘ d).filter fun n => k ≤ n).card := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [Multiset.filter_cons]
                by_cases hak : k ≤ a
                · simp [hak, add_comm]
                · simp [hak]
  · intro k hk
    have hstep :=
      xi_oracle_capacity_layercake_tail_completeness_capacity_step d k hk
    omega
  · intro k hk
    exact xi_oracle_capacity_layercake_tail_completeness_count_eq_tail_sub_tail d k

end Omega.Zeta
