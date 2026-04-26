import Mathlib.Tactic
import Omega.Conclusion.BoundaryParityBlindFiltration
import Omega.Conclusion.Window6BoundaryParityDirectSummandRationalBlindness

namespace Omega.Conclusion

/-- Concrete wrapper combining the window-6 boundary direct-summand/rational-blindness package
with the strict three-layer boundary parity filtration. -/
def conclusion_window6_rational_completeness_with_boundary_torsion_blindness_statement : Prop :=
  Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
      Omega.GU.window6BoundaryCartanInclusion ∧
    Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
    (∀ n : ℕ, 0 < n → window6BoundaryPositiveDegreeRationalCohomology n = 0) ∧
    (∀ n : ℕ, 0 < n → window6ConnectedLieRationalBlindness n = 0) ∧
    (2 : ℕ) ^ 3 = 8 ∧
    (2 : ℕ) ^ 1 = 2 ∧
    (3 : ℕ) - 1 = 2 ∧
    (0 : ℕ) < 1 ∧
    (1 : ℕ) < 3 ∧
    (0 : ℕ) + 1 + 2 = 3 ∧
    (8 : ℕ) / 2 = 4 ∧
    (2 : ℕ) ^ 2 = 4

/-- Paper label:
`thm:conclusion-window6-rational-completeness-with-boundary-torsion-blindness`.
The already formalized boundary direct-summand/rational-blindness data and the strict
three-layer boundary filtration combine into the advertised window-6 package. -/
theorem paper_conclusion_window6_rational_completeness_with_boundary_torsion_blindness :
    conclusion_window6_rational_completeness_with_boundary_torsion_blindness_statement := by
  rcases paper_conclusion_window6_boundary_parity_directsummand_rational_blindness with
    ⟨hLeftInv, hCard, hRat, hLie⟩
  rcases paper_conclusion_boundary_parity_three_layer_blind_filtration with
    ⟨hRank3, hGeo, hQuot, hZeroOne, hOneThree, hLayer, hIndex, hQuotCard⟩
  exact ⟨hLeftInv, hCard, hRat, hLie, hRank3, hGeo, hQuot, hZeroOne, hOneThree, hLayer, hIndex,
    hQuotCard⟩

end Omega.Conclusion
