import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.M2Level3Delta0RamificationSplitting

namespace Omega.Conclusion

/-- A concrete `Δ₀` transvection on the audited four-dimensional `𝔽₃`-homology model. -/
def conclusion_m2_level3_delta0_inertia_fixed_geometry_transvection :
    M2Level3Homology → M2Level3Homology := fun v i =>
  if i = 0 then v 0 + v 1 else v i

/-- Paper label: `prop:conclusion-m2-level3-delta0-inertia-fixed-geometry`. -/
theorem paper_conclusion_m2_level3_delta0_inertia_fixed_geometry :
    conclusion_m2_level3_delta0_inertia_fixed_geometry_transvection 0 = 0 ∧
      delta0ProjectiveOneCycles = 13 ∧
      delta0ProjectiveThreeCycles = 9 ∧
      delta0ProjectiveTotalObjects = delta0ProjectiveOneCycles + 3 * delta0ProjectiveThreeCycles ∧
      delta0LagrangianOneCycles = 4 ∧
      delta0LagrangianThreeCycles = 12 ∧
      delta0LagrangianTotalObjects =
        delta0LagrangianOneCycles + 3 * delta0LagrangianThreeCycles ∧
      delta0FlagOneCycles = 16 ∧
      delta0FlagThreeCycles = 48 ∧
      delta0FlagTotalObjects = delta0FlagOneCycles + 3 * delta0FlagThreeCycles := by
  rcases paper_conclusion_m2_level3_delta0_ramification_splitting with
    ⟨hProj1, hProj3, hLag1, hLag3, hFlag1, hFlag3, _, _⟩
  have hzero :
      conclusion_m2_level3_delta0_inertia_fixed_geometry_transvection 0 = 0 := by
    funext i
    by_cases h : i = 0
    · simp [conclusion_m2_level3_delta0_inertia_fixed_geometry_transvection, h]
    · simp [conclusion_m2_level3_delta0_inertia_fixed_geometry_transvection, h]
  refine ⟨hzero, hProj1, hProj3, ?_, hLag1, hLag3, ?_, hFlag1, hFlag3, ?_⟩
  · rw [hProj1, hProj3]
    norm_num [delta0ProjectiveTotalObjects]
  · rw [hLag1, hLag3]
    norm_num [delta0LagrangianTotalObjects]
  · rw [hFlag1, hFlag3]
    norm_num [delta0FlagTotalObjects]

end Omega.Conclusion
