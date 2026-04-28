import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

private lemma
    conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_min_pred_add_tail
    (n T : ℕ) (hT : 1 ≤ T) :
    min n (T - 1) + (if T ≤ n then 1 else 0) = min n T := by
  by_cases hle : T ≤ n
  · have hpred : T - 1 ≤ n := by omega
    rw [Nat.min_eq_right hpred, Nat.min_eq_right hle]
    simp [hle]
    omega
  · have hnT : n ≤ T := by omega
    have hnPred : n ≤ T - 1 := by omega
    rw [Nat.min_eq_left hnPred, Nat.min_eq_left hnT]
    simp [hle]

private lemma
    conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_capacity_step
    (s : Multiset ℕ) (T : ℕ) (hT : 1 ≤ T) :
    (s.map fun n => min n T).sum =
      (s.map fun n => min n (T - 1)).sum + (s.filter fun n => T ≤ n).card := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons n s ih =>
      by_cases hn : T ≤ n
      · simp [hn, ih]
        have hmin :=
          conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_min_pred_add_tail
            n T hT
        simp [hn] at hmin
        omega
      · simp [hn, ih]
        have hmin :=
          conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_min_pred_add_tail
            n T hT
        simp [hn] at hmin
        omega

private lemma
    conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_tail_eq_capacity_sub
    (s : Multiset ℕ) (T : ℕ) (hT : 1 ≤ T) :
    (s.filter fun n => T ≤ n).card =
      (s.map fun n => min n T).sum - (s.map fun n => min n (T - 1)).sum := by
  have hstep :=
    conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_capacity_step s T hT
  omega

private lemma
    conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_count_eq_tail_sub
    (s : Multiset ℕ) (k : ℕ) :
    s.count k = (s.filter fun n => k ≤ n).card -
      (s.filter fun n => k < n).card := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons n s ih =>
      have htailLe :
          (s.filter fun n => k < n).card ≤ (s.filter fun n => k ≤ n).card := by
        exact Multiset.card_le_card
          (s.monotone_filter_right fun n hn => by omega)
      by_cases hk : k = n
      · subst hk
        simp [ih]
        omega
      · by_cases hle : k ≤ n
        · have hlt : k < n := by omega
          simp [hk, hle, hlt, ih]
        · have hnlt : ¬k < n := by omega
          simp [hk, hle, hnlt, ih]

/-- Paper label:
`thm:conclusion-oracle-capacity-determines-bell-mobius-intermediate-system`. -/
theorem paper_conclusion_oracle_capacity_determines_bell_mobius_intermediate_system
    (d e : Multiset ℕ) (hposd : ∀ n ∈ d, 0 < n) (hpose : ∀ n ∈ e, 0 < n)
    (hcap : ∀ T : ℕ, 1 ≤ T →
      (d.map fun n => min n T).sum = (e.map fun n => min n T).sum) :
    d = e := by
  classical
  refine Multiset.ext.mpr ?_
  intro k
  by_cases hk0 : k = 0
  · subst hk0
    have hd0 : d.count 0 = 0 := by
      apply Multiset.count_eq_zero_of_notMem
      intro hmem
      have := hposd 0 hmem
      omega
    have he0 : e.count 0 = 0 := by
      apply Multiset.count_eq_zero_of_notMem
      intro hmem
      have := hpose 0 hmem
      omega
    rw [hd0, he0]
  · have hk : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have hkSucc : 1 ≤ k + 1 := by omega
    have htail (T : ℕ) (hT : 1 ≤ T) :
        (d.filter fun n => T ≤ n).card = (e.filter fun n => T ≤ n).card := by
      rw [
        conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_tail_eq_capacity_sub
          d T hT,
        conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_tail_eq_capacity_sub
          e T hT,
        hcap T hT]
      by_cases hT0 : T = 1
      · subst hT0
        simp
      · have hTm1 : 1 ≤ T - 1 := by omega
        rw [hcap (T - 1) hTm1]
    rw [
      conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_count_eq_tail_sub
        d k,
      conclusion_oracle_capacity_determines_bell_mobius_intermediate_system_count_eq_tail_sub
        e k]
    have htailK := htail k hk
    have htailKS := htail (k + 1) hkSucc
    simp only [Nat.succ_le_iff] at htailKS
    rw [htailK, htailKS]

end Omega.Conclusion
