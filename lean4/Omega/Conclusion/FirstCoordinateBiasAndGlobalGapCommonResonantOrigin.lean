import Omega.Conclusion.FoldGoldenResonanceCollisionGapHardFloor

namespace Omega.Conclusion

noncomputable section

/-- The global collision hard floor and the local first-coordinate hard floor share the same
resonant-origin package.
    cor:conclusion-first-coordinate-bias-and-global-gap-common-resonant-origin -/
theorem paper_conclusion_first_coordinate_bias_and_global_gap_common_resonant_origin
    (firstCoordinateBiasHardFloor : Prop) (hfirst : firstCoordinateBiasHardFloor) :
    (∀ m : ℕ, 2 * singlepairResonanceConstant ^ (2 : ℕ) ≤
      foldbinScaledCollisionExcess conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
        m) ∧
      firstCoordinateBiasHardFloor := by
  exact ⟨paper_conclusion_fold_golden_resonance_collision_gap_hard_floor, hfirst⟩

end

end Omega.Conclusion
