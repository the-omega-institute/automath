namespace Omega.Zeta

/-- Paper label: `cor:xi-golden-w1-good-side-gap-to-single-box-optimum`. -/
theorem paper_xi_golden_w1_good_side_gap_to_single_box_optimum
    (eventualGoodSide positiveLimitGap : Prop)
    (hEventual : eventualGoodSide) (hGap : positiveLimitGap) :
    eventualGoodSide ∧ positiveLimitGap := by
  exact ⟨hEventual, hGap⟩

end Omega.Zeta
