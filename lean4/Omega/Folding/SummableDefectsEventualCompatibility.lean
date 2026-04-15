import Omega.Folding.SummableNatEventuallyZero

namespace Omega.Folding

open Finset

private theorem bounded_partial_sums_of_eventually_zero
    (δMass : ℕ → ℕ) :
    (∃ M, ∀ m, M ≤ m → δMass m = 0) →
      ∃ C, ∀ n, ∑ i ∈ Finset.range n, δMass i ≤ C := by
  rintro ⟨M, hM⟩
  refine ⟨∑ i ∈ Finset.range M, δMass i, ?_⟩
  intro n
  by_cases hMn : n ≤ M
  · simpa using Omega.Folding.SummableNatEventuallyZero.partial_sum_mono δMass hMn
  · have hMle : M ≤ n := Nat.le_of_lt (lt_of_not_ge hMn)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMle
    rw [Finset.sum_range_add]
    have hzero : ∑ i ∈ Finset.range k, δMass (M + i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _hi
      exact hM (M + i) (Nat.le_add_right _ _)
    simp [hzero]

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Fold eventual-compatibility corollary.
    cor:summable-defects-eventual-compatibility -/
theorem paper_fold_truncation_summable_defects_eventual_compatibility
    (δMass : ℕ → ℕ) (threshold : ℕ → Prop) (Lift : Prop)
    (hthreshold : ∀ m, δMass m = 0 ↔ threshold m)
    (hlift : (∃ M, ∀ m, M ≤ m → δMass m = 0) ↔ Lift) :
    (((∃ C, ∀ n, ∑ i ∈ Finset.range n, δMass i ≤ C) ↔
        (∃ M, ∀ m, M ≤ m → δMass m = 0)) ∧
      ((∃ M, ∀ m, M ≤ m → δMass m = 0) ↔
        (∃ M, ∀ m, M ≤ m → threshold m)) ∧
      ((∃ M, ∀ m, M ≤ m → δMass m = 0) ↔ Lift)) := by
  refine ⟨?_, ?_, hlift⟩
  · constructor
    · rintro ⟨C, hbd⟩
      exact Omega.Folding.SummableNatEventuallyZero.paper_fold_naive_prefix_lift_summable_core
        δMass C hbd
    · exact bounded_partial_sums_of_eventually_zero δMass
  · constructor
    · rintro ⟨M, hM⟩
      exact ⟨M, fun m hm => (hthreshold m).mp (hM m hm)⟩
    · rintro ⟨M, hM⟩
      exact ⟨M, fun m hm => (hthreshold m).mpr (hM m hm)⟩

end Omega.Folding
