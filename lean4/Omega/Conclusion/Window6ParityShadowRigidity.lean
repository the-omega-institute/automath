import Mathlib.Tactic
import Omega.Conclusion.Window6GeometricDiagonalBitResidualShadow
import Omega.Conclusion.Window6LowTwoRankEnvelopeForcedCompression
import Omega.Conclusion.Window6MultiplicityDecoratedPinnedDatumRigidity
import Omega.Conclusion.Window6PinnedDatumToralCompletionEightsector
import Omega.Conclusion.Window6ResidualTorsionShadowRationalBlindness

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-parity-shadow-rigidity`. -/
def conclusion_window6_parity_shadow_rigidity_statement : Prop :=
  Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
      Omega.GU.window6BoundaryCartanInclusion ∧
    (Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      Fintype.card Omega.Conclusion.Window6BoundaryCharacter = 8 ∧
      Fintype.card Omega.Conclusion.Window6OrbitParitySector = 16) ∧
    (Fintype.card (Fin 1) = 1 ∧ Fintype.card (Fin 1) = 1) ∧
    ((∀ n : ℕ, 0 < n → Omega.Conclusion.window6ConnectedLieRationalBlindness n = 0) ∧
      (∀ n : ℕ, 0 < n →
        Omega.Conclusion.window6BoundaryPositiveDegreeRationalCohomology n = 0)) ∧
    conclusion_window6_low_two_rank_envelope_forced_compression_low_rank_obstruction ∧
      conclusion_window6_low_two_rank_envelope_forced_compression_so10_kernel_bound

/-- Paper label: `thm:conclusion-window6-parity-shadow-rigidity`. -/
theorem paper_conclusion_window6_parity_shadow_rigidity :
    conclusion_window6_parity_shadow_rigidity_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact paper_conclusion_window6_multiplicity_decorated_pinned_datum_rigidity
  · rcases paper_conclusion_window6_pinned_datum_toral_completion_eightsector with
      ⟨_, hBoundary, hCharacter, hOrbit⟩
    exact ⟨hBoundary, hCharacter, hOrbit⟩
  · exact paper_conclusion_window6_geometric_diagonal_bit_residual_shadow
      (Fintype.card (Fin 1) = 1) (Fintype.card (Fin 1) = 1) (by simp) (by simp)
  · rcases paper_conclusion_window6_residual_torsion_shadow_rational_blindness with
      ⟨hLie, hBoundary⟩
    exact ⟨hLie, hBoundary⟩
  · exact paper_conclusion_window6_low_two_rank_envelope_forced_compression

end Omega.Conclusion
