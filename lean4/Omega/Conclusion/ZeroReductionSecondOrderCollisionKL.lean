import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zero-reduction-second-order-collision-kl`. -/
theorem paper_conclusion_zero_reduction_second_order_collision_kl
    (fold_zero_uncertainty collision_gap_second_order kl_gap_second_order
      maxfiber_excess_bound : Prop)
    (h0 : fold_zero_uncertainty)
    (hcollision : fold_zero_uncertainty → collision_gap_second_order)
    (hkl : fold_zero_uncertainty → kl_gap_second_order)
    (hmax : fold_zero_uncertainty → maxfiber_excess_bound) :
    collision_gap_second_order ∧ kl_gap_second_order ∧ maxfiber_excess_bound := by
  exact ⟨hcollision h0, hkl h0, hmax h0⟩

end Omega.Conclusion
