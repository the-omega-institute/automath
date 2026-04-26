import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-boolean-square-double-erosion`. -/
theorem paper_conclusion_window6_boolean_square_double_erosion :
    ({0, 34} : Finset ℕ) ⊂ ({0, 21, 34} : Finset ℕ) ∧
      ({0, 21, 34} : Finset ℕ) ⊂ ({0, 21, 34, 55} : Finset ℕ) := by
  constructor
  · constructor
    · intro x hx
      simp at hx ⊢
      omega
    · intro hsub
      have hmem : 21 ∈ ({0, 21, 34} : Finset ℕ) := by simp
      have hnot : 21 ∉ ({0, 34} : Finset ℕ) := by simp
      exact hnot (hsub hmem)
  · constructor
    · intro x hx
      simp at hx ⊢
      omega
    · intro hsub
      have hmem : 55 ∈ ({0, 21, 34, 55} : Finset ℕ) := by simp
      have hnot : 55 ∉ ({0, 21, 34} : Finset ℕ) := by simp
      exact hnot (hsub hmem)

end Omega.Conclusion
