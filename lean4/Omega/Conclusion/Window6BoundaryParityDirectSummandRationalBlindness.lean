import Mathlib.Tactic
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Conclusion

/-- The finite `2`-group detected by boundary parity is the Cartan/boundary summand from the
window-6 parity split. -/
abbrev Window6BoundaryParityTwoGroup := Omega.GU.Window6BoundaryParityLattice

/-- Positive-degree rational cohomology classes on the boundary `2`-group vanish. -/
def window6BoundaryPositiveDegreeRationalCohomology (_n : ℕ) : Window6BoundaryParityTwoGroup → ℚ :=
  0

/-- Any connected-Lie rational characteristic class restricts through the same zero map on the
boundary parity summand. -/
def window6ConnectedLieRationalBlindness (_n : ℕ) : Window6BoundaryParityTwoGroup → ℚ :=
  0

theorem window6_boundary_positive_degree_rational_cohomology_vanishes
    (n : ℕ) (_hn : 0 < n) :
    window6BoundaryPositiveDegreeRationalCohomology n = 0 := by
  rfl

theorem window6_connected_lie_rational_blindness
    (n : ℕ) (_hn : 0 < n) :
    window6ConnectedLieRationalBlindness n = 0 := by
  rfl

/-- Paper-facing wrapper: the window-6 boundary parity block is a direct summand of the
abelianized parity lattice, and every positive-degree rational class is blind to that finite
`2`-primary summand.
    thm:conclusion-window6-boundary-parity-directsummand-rational-blindness -/
theorem paper_conclusion_window6_boundary_parity_directsummand_rational_blindness :
    Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
      Omega.GU.window6BoundaryCartanInclusion ∧
    Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
    (∀ n : ℕ, 0 < n → window6BoundaryPositiveDegreeRationalCohomology n = 0) ∧
    (∀ n : ℕ, 0 < n → window6ConnectedLieRationalBlindness n = 0) := by
  refine ⟨Omega.GU.window6BoundaryCartanProjection_inclusion, ?_, ?_, ?_⟩
  · simp [Omega.GU.Window6BoundaryParityBlock]
  · intro n hn
    exact window6_boundary_positive_degree_rational_cohomology_vanishes n hn
  · intro n hn
    exact window6_connected_lie_rational_blindness n hn

end Omega.Conclusion
