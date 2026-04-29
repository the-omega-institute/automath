import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic
import Omega.Folding.Fold
import Omega.Folding.ZeckendorfSignature

namespace Omega.GU

open Omega

local instance : IsTrans Nat (fun a b ↦ b + 2 ≤ a) where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

local instance : Std.Irrefl (fun a b : Nat ↦ b + 2 ≤ a) where
  irrefl a h := by omega

/-- The Zeckendorf index set `S(n)` used in the paper statement. -/
def zeckendorf_no_carry_additivity_index_set (n : ℕ) : Finset ℕ :=
  (Nat.zeckendorf n).toFinset

/-- The shifted signature `Σ(n)` induced from the Zeckendorf indices by the rule `m = k + 2`. -/
def zeckendorf_no_carry_additivity_sigma (n : ℕ) : Finset ℕ :=
  ((Nat.zeckendorf n).map fun k => k + 2).toFinset

/-- The cross-gap paper statement: if every Zeckendorf index of `A` is at distance at least `2`
from every Zeckendorf index of `B`, then both the index set and the shifted signature are unions
of the two summands. -/
def zeckendorf_no_carry_additivity_statement (A B : ℕ) : Prop :=
  (∀ i ∈ Nat.zeckendorf A, ∀ j ∈ Nat.zeckendorf B, 2 ≤ Nat.dist i j) →
    zeckendorf_no_carry_additivity_index_set (A + B) =
        zeckendorf_no_carry_additivity_index_set A ∪
          zeckendorf_no_carry_additivity_index_set B ∧
      zeckendorf_no_carry_additivity_sigma (A + B) =
        zeckendorf_no_carry_additivity_sigma A ∪ zeckendorf_no_carry_additivity_sigma B

lemma zeckendorf_no_carry_additivity_internal_gap {l : List ℕ} (hRep : l.IsZeckendorfRep)
    {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : 2 ≤ Nat.dist a b := by
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · have hsucc : a + 1 ∉ l := Omega.X.not_mem_succ_of_mem_isZeckendorfRep hRep ha
    have hlt : a + 1 < b := by
      have hne : a + 1 ≠ b := by
        intro hEq
        exact hsucc (hEq ▸ hb)
      omega
    rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hab')]
    omega
  · have hsucc : b + 1 ∉ l := Omega.X.not_mem_succ_of_mem_isZeckendorfRep hRep hb
    have hlt : b + 1 < a := by
      have hne : b + 1 ≠ a := by
        intro hEq
        exact hsucc (hEq ▸ ha)
      omega
    rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hba')]
    omega

lemma zeckendorf_no_carry_additivity_concat_gap
    {s t : List ℕ} (hs : s.IsZeckendorfRep) (ht : t.IsZeckendorfRep)
    (hgap : ∀ i ∈ s, ∀ j ∈ t, 2 ≤ Nat.dist i j) :
    ∀ a ∈ s ++ t, ∀ b ∈ s ++ t, a ≠ b → 2 ≤ Nat.dist a b := by
  intro a ha b hb hab
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp hb with hb | hb
    · exact zeckendorf_no_carry_additivity_internal_gap hs ha hb hab
    · exact hgap a ha b hb
  · rcases List.mem_append.mp hb with hb | hb
    · rw [Nat.dist_comm]
      exact hgap b hb a ha
    · exact zeckendorf_no_carry_additivity_internal_gap ht ha hb hab

lemma zeckendorf_no_carry_additivity_sorted_union_rep
    {s t : List ℕ} (hs : s.IsZeckendorfRep) (ht : t.IsZeckendorfRep)
    (hgap : ∀ i ∈ s, ∀ j ∈ t, 2 ≤ Nat.dist i j) :
    ((s ++ t).mergeSort (· ≥ ·)).IsZeckendorfRep := by
  let u := (s ++ t).mergeSort (· ≥ ·)
  have hperm : List.Perm u (s ++ t) := List.mergeSort_perm _ _
  have hsNodup : s.Nodup := by
    have hs' : List.Pairwise (fun a b ↦ b + 2 ≤ a) (s ++ [0]) := by
      simpa [List.IsZeckendorfRep, List.isChain_iff_pairwise] using hs
    exact hs'.nodup.of_append_left
  have htNodup : t.Nodup := by
    have ht' : List.Pairwise (fun a b ↦ b + 2 ≤ a) (t ++ [0]) := by
      simpa [List.IsZeckendorfRep, List.isChain_iff_pairwise] using ht
    exact ht'.nodup.of_append_left
  have hDisjoint : List.Disjoint s t := by
    simp [List.disjoint_left]
    intro a ha hb
    have : 2 ≤ Nat.dist a a := hgap a ha a hb
    simp at this
  have huNodup : u.Nodup := by
    have hstNodup : (s ++ t).Nodup := hsNodup.append htNodup hDisjoint
    exact (List.Perm.nodup_iff hperm).2 hstNodup
  have huGapDist : List.Pairwise (fun a b => 2 ≤ Nat.dist a b) u := by
    rw [List.pairwise_iff_get]
    intro i j hij
    have hneq : u.get i ≠ u.get j := by
      intro hEq
      exact hij.ne ((huNodup.get_inj_iff).mp hEq)
    have hiMem : u.get i ∈ u := List.get_mem _ _
    have hjMem : u.get j ∈ u := List.get_mem _ _
    have hiMem' : u.get i ∈ s ++ t := (List.Perm.mem_iff hperm).mp hiMem
    have hjMem' : u.get j ∈ s ++ t := (List.Perm.mem_iff hperm).mp hjMem
    exact zeckendorf_no_carry_additivity_concat_gap hs ht hgap _ hiMem' _ hjMem' hneq
  have huSorted : List.Pairwise (· ≥ ·) u := by
    simpa [u] using (List.pairwise_mergeSort' (r := (· ≥ ·)) (s ++ t))
  have huGap : List.Pairwise (fun a b ↦ b + 2 ≤ a) u := by
    rw [List.pairwise_iff_get]
    intro i j hij
    have hge : u.get i ≥ u.get j := huSorted.rel_get_of_lt hij
    have hdist : 2 ≤ Nat.dist (u.get i) (u.get j) := huGapDist.rel_get_of_lt hij
    rw [Nat.dist_eq_sub_of_le_right hge] at hdist
    omega
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise]
  refine List.pairwise_append.2 ⟨huGap, List.pairwise_singleton (fun a b ↦ b + 2 ≤ a) 0, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  have ha' : a ∈ s ++ t := (List.Perm.mem_iff hperm).mp ha
  rcases List.mem_append.mp ha' with ha' | ha'
  · exact Omega.X.two_le_of_mem_isZeckendorfRep hs ha'
  · exact Omega.X.two_le_of_mem_isZeckendorfRep ht ha'

lemma zeckendorf_no_carry_additivity_sum_eq_sorted_union
    {s t : List ℕ} :
    (((s ++ t).mergeSort (· ≥ ·)).map Nat.fib).sum = (s.map Nat.fib).sum + (t.map Nat.fib).sum := by
  have hperm :
      List.Perm (((s ++ t).mergeSort (· ≥ ·)).map Nat.fib) ((s ++ t).map Nat.fib) := by
    simpa [List.map_append] using
      (List.Perm.map Nat.fib (List.mergeSort_perm (s ++ t) (· ≥ ·)))
  haveI : LeftCommutative Nat.add := ⟨Nat.add_left_comm⟩
  calc
    (((s ++ t).mergeSort (· ≥ ·)).map Nat.fib).sum = ((s ++ t).map Nat.fib).sum := by
      simpa [List.sum] using hperm.foldr_eq (f := Nat.add) 0
    _ = (s.map Nat.fib).sum + (t.map Nat.fib).sum := by
      simp [List.map_append, List.sum_append]

/-- Paper label: `thm:zeckendorf-no-carry-additivity`. If the Zeckendorf index sets of `A` and
`B` are pairwise separated by distance at least `2`, then the index set and the shifted signature
of `A + B` are exactly the unions of those of `A` and `B`. -/
theorem paper_zeckendorf_no_carry_additivity (A B : ℕ) :
    zeckendorf_no_carry_additivity_statement A B := by
  intro hgap
  let s := Nat.zeckendorf A
  let t := Nat.zeckendorf B
  let u := (s ++ t).mergeSort (· ≥ ·)
  have hs : s.IsZeckendorfRep := Nat.isZeckendorfRep_zeckendorf A
  have ht : t.IsZeckendorfRep := Nat.isZeckendorfRep_zeckendorf B
  have hu : u.IsZeckendorfRep := zeckendorf_no_carry_additivity_sorted_union_rep hs ht hgap
  have hA : (s.map Nat.fib).sum = A := Nat.sum_zeckendorf_fib A
  have hB : (t.map Nat.fib).sum = B := Nat.sum_zeckendorf_fib B
  have hsum : (u.map Nat.fib).sum = A + B := by
    rw [zeckendorf_no_carry_additivity_sum_eq_sorted_union, hA, hB]
  have hzeck : Nat.zeckendorf (A + B) = u := by
    rw [← hsum]
    exact Nat.zeckendorf_sum_fib hu
  have hindex :
      zeckendorf_no_carry_additivity_index_set (A + B) =
        zeckendorf_no_carry_additivity_index_set A ∪
          zeckendorf_no_carry_additivity_index_set B := by
    unfold zeckendorf_no_carry_additivity_index_set
    rw [hzeck]
    simpa [s, t] using List.toFinset_eq_of_perm _ _ (List.mergeSort_perm (s ++ t) (· ≥ ·))
  have hsigma :
      zeckendorf_no_carry_additivity_sigma (A + B) =
        zeckendorf_no_carry_additivity_sigma A ∪ zeckendorf_no_carry_additivity_sigma B := by
    unfold zeckendorf_no_carry_additivity_sigma
    rw [hzeck]
    calc
      List.toFinset (u.map fun k => k + 2) = List.toFinset ((s ++ t).map fun k => k + 2) := by
        exact List.toFinset_eq_of_perm _ _ <|
          List.Perm.map (fun k => k + 2) (List.mergeSort_perm (s ++ t) (· ≥ ·))
      _ = List.toFinset (s.map fun k => k + 2) ∪ List.toFinset (t.map fun k => k + 2) := by
        simp [List.map_append, List.toFinset_append]
  exact ⟨hindex, hsigma⟩

end Omega.GU
