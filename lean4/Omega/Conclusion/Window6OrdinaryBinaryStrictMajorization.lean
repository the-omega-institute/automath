import Mathlib.Tactic

namespace Omega.Conclusion

private def window6OrdinaryFiberSizes : List Nat :=
  [5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]

private def window6BinaryFiberSizes : List Nat :=
  [4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]

private theorem window6OrdinaryBinary_total_mass :
    window6OrdinaryFiberSizes.sum = window6BinaryFiberSizes.sum := by
  native_decide

private theorem window6OrdinaryBinary_prefix_domination (k : Nat) (hk1 : 1 ≤ k)
    (hk2 : k ≤ window6OrdinaryFiberSizes.length) :
    (window6OrdinaryFiberSizes.take k).sum ≥ (window6BinaryFiberSizes.take k).sum := by
  have hk21 : k ≤ 21 := by
    simpa [window6OrdinaryFiberSizes] using hk2
  interval_cases k <;> native_decide

private theorem window6OrdinaryBinary_strict_step :
    ∃ k : Nat, 1 ≤ k ∧ k < window6OrdinaryFiberSizes.length ∧
      (window6OrdinaryFiberSizes.take k).sum > (window6BinaryFiberSizes.take k).sum := by
  refine ⟨1, ?_⟩
  native_decide

private theorem window6OrdinaryBinaryStrictMajorization_certificate :
    window6OrdinaryFiberSizes.sum = window6BinaryFiberSizes.sum ∧
      (∀ k : Nat, 1 ≤ k → k ≤ window6OrdinaryFiberSizes.length →
        (window6OrdinaryFiberSizes.take k).sum ≥ (window6BinaryFiberSizes.take k).sum) ∧
      (∃ k : Nat, 1 ≤ k ∧ k < window6OrdinaryFiberSizes.length ∧
        (window6OrdinaryFiberSizes.take k).sum > (window6BinaryFiberSizes.take k).sum) := by
  exact ⟨window6OrdinaryBinary_total_mass, window6OrdinaryBinary_prefix_domination,
    window6OrdinaryBinary_strict_step⟩

/-- Paper label: `thm:conclusion-window6-ordinary-binary-strict-majorization`. -/
theorem paper_conclusion_window6_ordinary_binary_strict_majorization :
    let ord : List Nat := [5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]
    let bin : List Nat := [4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]
    ord.sum = bin.sum ∧
      (∀ k : Nat, 1 ≤ k → k ≤ ord.length → (ord.take k).sum ≥ (bin.take k).sum) ∧
      (∃ k : Nat, 1 ≤ k ∧ k < ord.length ∧ (ord.take k).sum > (bin.take k).sum) := by
  simpa [window6OrdinaryFiberSizes, window6BinaryFiberSizes] using
    window6OrdinaryBinaryStrictMajorization_certificate

end Omega.Conclusion
