import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-screen-zero-one-local-law-effective-resistance`. -/
theorem paper_conclusion_screen_zero_one_local_law_effective_resistance {E : Type*}
    (cross bridge : E → Prop) (rankInc : E → ℕ) (κ : E → ℝ)
    (h_same_rank : ∀ e, ¬ cross e → rankInc e = 0)
    (h_cross_rank : ∀ e, cross e → rankInc e = 1)
    (h_same_kappa : ∀ e, ¬ cross e → κ e = 0)
    (h_cross_bridge : ∀ e, cross e → (κ e = 1 ↔ bridge e))
    (h_cross_nonbridge : ∀ e, cross e → (0 < κ e ∧ κ e < 1 ↔ ¬ bridge e)) :
    (∀ e, κ e = 0 ↔ rankInc e = 0) ∧ (∀ e, cross e → rankInc e = 1) ∧
      (∀ e, cross e → (κ e = 1 ↔ bridge e)) ∧
        (∀ e, cross e → (0 < κ e ∧ κ e < 1 ↔ ¬ bridge e)) := by
  refine ⟨?_, h_cross_rank, h_cross_bridge, h_cross_nonbridge⟩
  intro e
  by_cases hcross : cross e
  · constructor
    · intro hk_zero
      exfalso
      by_cases hbridge : bridge e
      · have hk_one : κ e = 1 := (h_cross_bridge e hcross).mpr hbridge
        linarith
      · have hk_pos : 0 < κ e := ((h_cross_nonbridge e hcross).mpr hbridge).1
        linarith
    · intro hr_zero
      exfalso
      have hr_one : rankInc e = 1 := h_cross_rank e hcross
      omega
  · constructor
    · intro _hκ
      exact h_same_rank e hcross
    · intro _hr
      exact h_same_kappa e hcross

end Omega.Conclusion
