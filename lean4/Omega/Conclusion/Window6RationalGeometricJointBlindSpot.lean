import Omega.Conclusion.BoundaryParityBlindFiltration

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-rational-geometric-joint-blind-spot`. -/
theorem paper_conclusion_window6_rational_geometric_joint_blind_spot :
    (2 : Nat) ^ 3 = 8 ∧ (2 : Nat) ^ 1 = 2 ∧ (2 : Nat) ^ 2 = 4 ∧
      (8 : Nat) / 2 = 4 := by
  have h := paper_conclusion_boundary_parity_three_layer_blind_filtration
  omega

end Omega.Conclusion
