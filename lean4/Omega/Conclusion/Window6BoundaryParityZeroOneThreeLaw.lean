import Mathlib.Tactic
import Omega.Conclusion.BoundaryParityBlindFiltration
import Omega.Conclusion.Elementary2GroupMinimalTorusDimension
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness

namespace Omega.Conclusion

/-- Rational continuous certificates see none of the window-`6` boundary parity. -/
def conclusion_window6_boundary_parity_zero_one_three_law_rational_rank : ℕ :=
  0

/-- Strong local geometric certificates only retain the diagonal parity direction. -/
def conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank : ℕ :=
  1

/-- A faithful torus-holonomy realization needs the full rank-`3` boundary parity block. -/
def conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank : ℕ :=
  3

/-- Paper-facing `(0,1,3)` channel law for window-`6` boundary parity. -/
def conclusion_window6_boundary_parity_zero_one_three_law_statement : Prop :=
  conclusion_window6_boundary_parity_zero_one_three_law_rational_rank = 0 ∧
    conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank = 1 ∧
    conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank = 3 ∧
    Fintype.card Omega.GU.Window6BoundaryParityBlock =
      conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank ∧
    (∀ n : ℕ, 0 < n → window6BoundaryPositiveDegreeRationalCohomology n = 0) ∧
    (∀ n : ℕ, 0 < n → window6ConnectedLieRationalBlindness n = 0) ∧
    (2 : ℕ) ^ conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank = 2 ∧
    (0 : ℕ) < conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank ∧
    conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank <
      conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank ∧
    (∀ r,
      conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model
          conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank r →
        conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank ≤ r) ∧
    conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model
      conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank
      conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank

/-- Paper label: `thm:conclusion-window6-boundary-parity-zero-one-three-law`. The already verified
rational-blindness, geometric-diagonal, and minimal-torus-rank packages combine into the exact
window-`6` channel trichotomy `0/1/3`. -/
theorem paper_conclusion_window6_boundary_parity_zero_one_three_law :
    conclusion_window6_boundary_parity_zero_one_three_law_statement := by
  rcases paper_conclusion_window6_boundary_parity_directsummand_rational_blindness with
    ⟨_, hCard, hRat, hLie⟩
  rcases paper_conclusion_boundary_parity_three_layer_blind_filtration with
    ⟨_, hGeo, _, hZeroOne, hOneThree, _, _, _⟩
  rcases paper_conclusion_elementary_2group_minimal_torus_dimension 3 with
    ⟨hFaithfulLower, hFaithfulSharp⟩
  exact ⟨rfl, rfl, rfl,
    by
      simpa [conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank] using
        hCard,
    hRat, hLie,
    by
      simpa [conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank] using hGeo,
    by
      simpa [conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank] using hZeroOne,
    by
      simpa [conclusion_window6_boundary_parity_zero_one_three_law_geometric_rank,
        conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank] using hOneThree,
    by
      intro r hr
      simpa [conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank] using
        hFaithfulLower r hr,
    by
      simpa [conclusion_window6_boundary_parity_zero_one_three_law_faithful_torus_rank] using
        hFaithfulSharp⟩

end Omega.Conclusion
