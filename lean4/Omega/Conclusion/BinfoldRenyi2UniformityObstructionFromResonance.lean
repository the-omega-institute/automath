import Omega.Conclusion.FoldGoldenResonanceCollisionGapHardFloor
import Omega.Conclusion.FoldbinRemoveMainResonancePeaksStillDiverges

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-renyi2-uniformity-obstruction-from-resonance`. -/
theorem paper_conclusion_binfold_renyi2_uniformity_obstruction_from_resonance :
    (∀ m : ℕ,
      2 * Omega.Conclusion.singlepairResonanceConstant ^ (2 : ℕ) ≤
        Omega.Conclusion.foldbinScaledCollisionExcess
          Omega.Conclusion.conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m) ∧
      Omega.Conclusion.foldbinMainResonanceContribution =
        2 * Omega.Conclusion.singlepairResonanceConstant ^ (2 : ℕ) := by
  refine ⟨?_, rfl⟩
  exact paper_conclusion_fold_golden_resonance_collision_gap_hard_floor

end Omega.Conclusion
