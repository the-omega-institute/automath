import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-foldbin-deep-padic-flatness-criterion`. -/
theorem paper_conclusion_foldbin_deep_padic_flatness_criterion
    {α : Type*} [Fintype α] (carry : α → ℕ) (valuationGap : ℕ)
    (hgap : valuationGap = ∑ a, carry a) :
    valuationGap = 0 ↔ ∀ a, carry a = 0 := by
  constructor
  · intro hzero a
    have hsum : (∑ a, carry a) = 0 := by
      rw [← hgap, hzero]
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset α)) (f := carry) (fun x _ => Nat.zero_le (carry x))).mp
        hsum a (by simp)
  · intro hzero
    rw [hgap]
    exact Finset.sum_eq_zero fun a _ => hzero a

end Omega.Conclusion
