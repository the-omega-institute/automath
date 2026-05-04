import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-middle-bin-boundary-separation`.
The encoded middle-bin words `{10, 18, 34, 42}` and boundary words `{33, 37, 41}` are disjoint,
and the stated uniform-mass identities reduce to rational arithmetic. -/
theorem paper_conclusion_window6_middle_bin_boundary_separation :
    (∀ w : ℕ, w ∈ ({10, 18, 34, 42} : Finset ℕ) →
      w ∉ ({33, 37, 41} : Finset ℕ)) ∧
      ((4 : ℚ) * 3) / 64 = 3 / 16 ∧
        ((3 : ℚ) * 2) / 64 = 3 / 32 ∧
          ((4 : ℚ) * 3) / 64 = 2 * (((3 : ℚ) * 2) / 64) := by
  constructor
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl | rfl | rfl <;> norm_num
  · norm_num

end Omega.Conclusion
