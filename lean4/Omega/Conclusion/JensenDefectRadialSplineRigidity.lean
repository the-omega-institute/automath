import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-jensen-defect-radial-spline-rigidity`. -/
theorem paper_conclusion_jensen_defect_radial_spline_rigidity {s : ℕ} (breaks : Fin s → ℝ)
    (jump : Fin s → ℕ) (Delta : ℝ → ℝ)
    (hDelta : ∀ x, Delta x = ∑ j : Fin s, (jump j : ℝ) * max (x - breaks j) 0) :
    (∀ x, Delta x = ∑ j : Fin s, (jump j : ℝ) * max (x - breaks j) 0) ∧
      (∀ x y, x ≤ y → Delta x ≤ Delta y) := by
  refine ⟨hDelta, ?_⟩
  intro x y hxy
  rw [hDelta x, hDelta y]
  exact Finset.sum_le_sum fun j _hj => by
    have hhinge : max (x - breaks j) 0 ≤ max (y - breaks j) 0 :=
      max_le_max (sub_le_sub_right hxy (breaks j)) le_rfl
    exact mul_le_mul_of_nonneg_left hhinge (Nat.cast_nonneg (jump j))

end Omega.Conclusion
