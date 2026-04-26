import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness
import Omega.Conclusion.Window6BoundarySuperselectionC3OrbitStratification

namespace Omega.Conclusion

/-- Concrete boundary package for the rational-blind/torsion-visible window-6 split. -/
structure conclusion_window6_boundary_rational_blind_torsion_superselection_data where
  positiveDegree : ℕ
  positiveDegree_pos : 0 < positiveDegree

namespace conclusion_window6_boundary_rational_blind_torsion_superselection_data

/-- Rational characteristic classes vanish on the boundary parity block in positive degree. -/
def rationalBlind
    (_D : conclusion_window6_boundary_rational_blind_torsion_superselection_data) : Prop :=
  ∀ n : ℕ, 0 < n → window6ConnectedLieRationalBlindness n = 0

/-- The boundary parity character decomposition has eight sectors. -/
def eightfoldSuperselection
    (_D : conclusion_window6_boundary_rational_blind_torsion_superselection_data) : Prop :=
  Fintype.card Window6BoundaryCharacter = 8

end conclusion_window6_boundary_rational_blind_torsion_superselection_data

/-- Paper label:
`thm:conclusion-window6-boundary-rational-blind-torsion-superselection`. -/
theorem paper_conclusion_window6_boundary_rational_blind_torsion_superselection
    (D : conclusion_window6_boundary_rational_blind_torsion_superselection_data) :
    D.rationalBlind ∧ D.eightfoldSuperselection := by
  rcases paper_conclusion_window6_boundary_parity_directsummand_rational_blindness with
    ⟨_, _, _, hLie⟩
  refine ⟨hLie, ?_⟩
  change Fintype.card Window6BoundaryCharacter = 8
  native_decide

end Omega.Conclusion
