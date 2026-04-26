import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-second-order-two-node-blindness`. -/
theorem paper_conclusion_poisson_second_order_two_node_blindness :
    ∀ y : ℝ,
      2 * (3 * y ^ 2 - 1) / (1 + y ^ 2) ^ 2 = 0 ↔
        y ^ 2 = (1 : ℝ) / 3 := by
  intro y
  have hden : (1 + y ^ 2) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    field_simp [hden] at h
    nlinarith
  · intro h
    field_simp [hden]
    nlinarith

end Omega.Conclusion
