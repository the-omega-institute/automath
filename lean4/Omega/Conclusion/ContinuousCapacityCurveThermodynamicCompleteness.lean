import Mathlib.Tactic

namespace Omega.Conclusion

private lemma conclusion_continuous_capacity_curve_thermodynamic_completeness_min_succ
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

private lemma conclusion_continuous_capacity_curve_thermodynamic_completeness_capacity_step
    (d : Multiset ℕ) (k : ℕ) (hk : 1 ≤ k) :
    (d.map fun n => Nat.min n k).sum =
      (d.map fun n => Nat.min n (k - 1)).sum + (d.filter fun n => k ≤ n).card := by
  induction d using Multiset.induction_on with
  | empty =>
      simp
  | cons a d ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
      rw [Multiset.filter_cons]
      rw [conclusion_continuous_capacity_curve_thermodynamic_completeness_min_succ a k hk, ih]
      by_cases hak : k ≤ a
      · simp [hak, add_assoc, add_comm, add_left_comm]
      · simp [hak, add_comm, add_left_comm]

private lemma conclusion_continuous_capacity_curve_thermodynamic_completeness_tail_card_mono
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

private lemma conclusion_continuous_capacity_curve_thermodynamic_completeness_count_eq_tail_sub_tail
    (d : Multiset ℕ) (k : ℕ) :
    d.count k = (d.filter fun n => k ≤ n).card - (d.filter fun n => k + 1 ≤ n).card := by
  induction d using Multiset.induction_on with
  | empty =>
      simp
  | cons a d ih =>
      rw [Multiset.count_cons, Multiset.filter_cons, Multiset.filter_cons]
      have hmono :=
        conclusion_continuous_capacity_curve_thermodynamic_completeness_tail_card_mono d k
      have hmono' :
          (d.filter fun x => k < x).card ≤ (d.filter fun n => k ≤ n).card := by
        simpa [Nat.succ_le_iff] using hmono
      by_cases hak : k ≤ a
      · by_cases hsak : k + 1 ≤ a
        · have hak_ne : ¬k = a := by omega
          simp [hak, hsak, hak_ne, ih]
        · have haeq : a = k := by omega
          simp [hak, hsak, haeq, ih]
          omega
      · have hsak : ¬k + 1 ≤ a := by omega
        have hak_ne : ¬k = a := by omega
        simp [hak, hsak, hak_ne, ih]

/-- Paper label:
`thm:conclusion-continuous-capacity-curve-thermodynamic-completeness`. -/
theorem paper_conclusion_continuous_capacity_curve_thermodynamic_completeness
    (d e : Multiset ℕ) (hposd : ∀ n ∈ d, 0 < n) (hpose : ∀ n ∈ e, 0 < n)
    (hcap : ∀ T : ℕ, 1 ≤ T →
      (d.map fun n => Nat.min n T).sum = (e.map fun n => Nat.min n T).sum) :
    (∀ k : ℕ, d.count k = e.count k) ∧ d = e := by
  have htail : ∀ k : ℕ, 1 ≤ k →
      (d.filter fun n => k ≤ n).card = (e.filter fun n => k ≤ n).card := by
    intro k hk
    have hd :=
      conclusion_continuous_capacity_curve_thermodynamic_completeness_capacity_step d k hk
    have he :=
      conclusion_continuous_capacity_curve_thermodynamic_completeness_capacity_step e k hk
    have hde :
        (d.map fun n => Nat.min n k).sum -
            (d.map fun n => Nat.min n (k - 1)).sum =
          (e.map fun n => Nat.min n k).sum -
            (e.map fun n => Nat.min n (k - 1)).sum := by
      by_cases hkone : k = 1
      · subst hkone
        simp [hcap 1 (by norm_num)]
      · have hkprev : 1 ≤ k - 1 := by omega
        rw [hcap k hk, hcap (k - 1) hkprev]
    omega
  have hcounts : ∀ k : ℕ, d.count k = e.count k := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      have hd0 : 0 ∉ d := by
        intro hmem
        have hpos := hposd 0 hmem
        omega
      have he0 : 0 ∉ e := by
        intro hmem
        have hpos := hpose 0 hmem
        omega
      simp [Multiset.count_eq_zero_of_notMem hd0, Multiset.count_eq_zero_of_notMem he0]
    · have hk : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
      have hksucc : 1 ≤ k + 1 := by omega
      have hd :=
        conclusion_continuous_capacity_curve_thermodynamic_completeness_count_eq_tail_sub_tail
          d k
      have he :=
        conclusion_continuous_capacity_curve_thermodynamic_completeness_count_eq_tail_sub_tail
          e k
      rw [hd, he, htail k hk, htail (k + 1) hksucc]
  exact ⟨hcounts, Multiset.ext.mpr hcounts⟩

end Omega.Conclusion
