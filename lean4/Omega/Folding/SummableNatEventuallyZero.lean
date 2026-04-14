import Mathlib.Tactic

namespace Omega.Folding.SummableNatEventuallyZero

open Finset

/-- Partial sums of a Nat-valued sequence are monotone in the upper bound.
    prop:fold-naive-prefix-lift -/
theorem partial_sum_mono (a : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    ∑ i ∈ Finset.range m, a i ≤ ∑ i ∈ Finset.range n, a i :=
  Finset.sum_le_sum_of_subset
    (fun _ hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h))

/-- Helper: if all partial sums are ≤ C and `S ⊆ range n` has all `a s > 0`,
    then `|S| ≤ C`.
    prop:fold-naive-prefix-lift -/
theorem card_pos_support_le (a : ℕ → ℕ) (C : ℕ)
    (hbd : ∀ n, ∑ i ∈ Finset.range n, a i ≤ C) (n : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Finset.range n) (hpos : ∀ k ∈ S, 0 < a k) :
    S.card ≤ C := by
  have hle : S.card ≤ ∑ k ∈ S, a k := by
    calc S.card = ∑ _k ∈ S, 1 := by simp
      _ ≤ ∑ k ∈ S, a k := Finset.sum_le_sum (fun k hk => hpos k hk)
  have hle2 : (∑ k ∈ S, a k) ≤ ∑ i ∈ Finset.range n, a i :=
    Finset.sum_le_sum_of_subset hS
  have hbdn := hbd n
  omega

/-- Define the "positive support within range N" as a Finset.
    prop:fold-naive-prefix-lift -/
def posSupportRange (a : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => 0 < a i)

/-- Bounded partial sums imply eventually zero.
    prop:fold-naive-prefix-lift -/
theorem eventually_zero_of_partial_sum_bounded
    (a : ℕ → ℕ) (C : ℕ) (hbd : ∀ n, ∑ i ∈ Finset.range n, a i ≤ C) :
    ∃ N, ∀ n, N ≤ n → a n = 0 := by
  by_contra hcon
  push_neg at hcon
  -- Step: for any `k`, we can find `N` with `(posSupportRange a N).card ≥ k`.
  have step : ∀ k, ∃ N, k ≤ (posSupportRange a N).card := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨m, hm_ge, hm_ne⟩ := hcon N
      refine ⟨m + 1, ?_⟩
      unfold posSupportRange at hN ⊢
      have hm_pos : 0 < a m := Nat.pos_of_ne_zero hm_ne
      have hmem : m ∈ (Finset.range (m + 1)).filter (fun i => 0 < a i) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self m), hm_pos⟩
      have hsub : (Finset.range N).filter (fun i => 0 < a i) ⊆
          (Finset.range (m + 1)).filter (fun i => 0 < a i) := by
        intro x hx
        rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨by omega, hx.2⟩
      have hnot_mem : m ∉ (Finset.range N).filter (fun i => 0 < a i) := by
        rw [Finset.mem_filter, Finset.mem_range]
        rintro ⟨hm_lt, _⟩
        omega
      have hssub : (Finset.range N).filter (fun i => 0 < a i) ⊂
          (Finset.range (m + 1)).filter (fun i => 0 < a i) :=
        ⟨hsub, fun hcontra => hnot_mem (hcontra hmem)⟩
      have hcard_lt := Finset.card_lt_card hssub
      omega
  obtain ⟨N, hN⟩ := step (C + 1)
  have hsub : posSupportRange a N ⊆ Finset.range N := by
    unfold posSupportRange
    exact Finset.filter_subset _ _
  have hpos : ∀ k ∈ posSupportRange a N, 0 < a k := by
    intro k hk
    unfold posSupportRange at hk
    exact (Finset.mem_filter.mp hk).2
  have hcard_le := card_pos_support_le a C hbd N (posSupportRange a N) hsub hpos
  omega

/-- Paper package: fold naive prefix lift — summable core.
    prop:fold-naive-prefix-lift -/
theorem paper_fold_naive_prefix_lift_summable_core
    (a : ℕ → ℕ) (C : ℕ) (hbd : ∀ n, ∑ i ∈ Finset.range n, a i ≤ C) :
    ∃ N, ∀ n, N ≤ n → a n = 0 :=
  eventually_zero_of_partial_sum_bounded a C hbd

end Omega.Folding.SummableNatEventuallyZero
