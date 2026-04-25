import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-window6-residual-torsion-shadow-rational-blindness`. The two positive-degree
rational blindness components are projections of the boundary-parity direct-summand theorem. -/
theorem paper_conclusion_window6_residual_torsion_shadow_rational_blindness :
    (∀ n : ℕ, 0 < n → Omega.Conclusion.window6ConnectedLieRationalBlindness n = 0) ∧
      (∀ n : ℕ, 0 < n →
        Omega.Conclusion.window6BoundaryPositiveDegreeRationalCohomology n = 0) := by
  rcases paper_conclusion_window6_boundary_parity_directsummand_rational_blindness with
    ⟨_, _, hBoundary, hLie⟩
  exact ⟨hLie, hBoundary⟩

end Omega.Conclusion
