import Mathlib.Tactic
import Omega.Conclusion.M2Level3Delta0RamificationSplitting

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-m2-level3-delta0-ramification-pushforward`. The pushforward
coefficients above `Δ₀` are twice the counted ramified `3`-cycle components, and the `Δ₁`
contribution vanishes because the monodromy there is trivial. -/
theorem paper_conclusion_m2_level3_delta0_ramification_pushforward :
    2 * delta0ProjectiveThreeCycles = 18 ∧
      2 * delta0LagrangianThreeCycles = 24 ∧
      2 * delta0FlagThreeCycles = 96 ∧
      delta1Monodromy = id := by
  rcases paper_conclusion_m2_level3_delta0_ramification_splitting with
    ⟨_, hProj3, _, hLag3, _, hFlag3, _, hDelta1⟩
  refine ⟨?_, ?_, ?_, hDelta1⟩
  · rw [hProj3]
  · rw [hLag3]
  · rw [hFlag3]

end Omega.Conclusion
