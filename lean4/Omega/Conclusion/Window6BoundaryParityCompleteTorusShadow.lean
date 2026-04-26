import Omega.Conclusion.Window6PinnedDatumToralCompletionEightsector
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-boundary-parity-complete-torus-shadow`. -/
theorem paper_conclusion_window6_boundary_parity_complete_torus_shadow :
    (Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
        Omega.GU.window6BoundaryCartanInclusion ∧
      Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
      Fintype.card Omega.Conclusion.Window6BoundaryCharacter = 8 ∧
      Fintype.card Omega.Conclusion.Window6OrbitParitySector = 16) ∧
      (∀ boundary,
        Omega.GU.window6AbelianizedParityChargeSplit
            (Omega.GU.window6BoundaryCartanInclusion boundary) =
          ((0, 0), boundary)) := by
  refine ⟨paper_conclusion_window6_pinned_datum_toral_completion_eightsector, ?_⟩
  rcases Omega.GU.paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨_, _, _, _, _, _, _, _, _, _, hSplit⟩
  exact hSplit

end Omega.Conclusion
