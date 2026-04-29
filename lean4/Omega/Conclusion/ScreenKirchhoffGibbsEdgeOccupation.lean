import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-kirchhoff-gibbs-edge-occupation`. -/
theorem paper_conclusion_screen_kirchhoff_gibbs_edge_occupation
    (edgeOccupation logDerivative conductance effectiveResistance : ℝ)
    (h_deriv : edgeOccupation = logDerivative)
    (h_resistance : logDerivative = conductance * effectiveResistance) :
    edgeOccupation = logDerivative ∧ edgeOccupation = conductance * effectiveResistance := by
  exact ⟨h_deriv, h_deriv.trans h_resistance⟩

end Omega.Conclusion
