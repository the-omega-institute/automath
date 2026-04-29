import Mathlib.Tactic
import Omega.Conclusion.M2Level3Delta0RamificationSplitting
import Omega.Conclusion.M2Level3XiInertiaPermutationRamification

namespace Omega.Conclusion

/-- The pushforward coefficients `(Δ₀, Δ₁, Ξ)` for the Klingen cover. -/
def conclusion_m2_level3_xi_ramification_pushforward_klingen : ℕ × ℕ × ℕ :=
  (2 * delta0ProjectiveThreeCycles, 0,
    conclusion_m2_level3_xi_inertia_permutation_ramification_projective_two_cycles)

/-- The pushforward coefficients `(Δ₀, Δ₁, Ξ)` for the Siegel cover. -/
def conclusion_m2_level3_xi_ramification_pushforward_siegel : ℕ × ℕ × ℕ :=
  (2 * delta0LagrangianThreeCycles, 0,
    conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_two_cycles)

/-- The pushforward coefficients `(Δ₀, Δ₁, Ξ)` for the flag cover. -/
def conclusion_m2_level3_xi_ramification_pushforward_flag : ℕ × ℕ × ℕ :=
  (2 * delta0FlagThreeCycles, 0,
    conclusion_m2_level3_xi_inertia_permutation_ramification_flag_two_cycles)

/-- Paper label: `cor:conclusion-m2-level3-xi-ramification-pushforward`. The `Δ₀`
contributions are twice the previously counted `3`-cycle branches, the `Ξ` contributions are the
transposition counts from the bielliptic inertia permutation theorem, and the `Δ₁`
contributions vanish because the local monodromy is trivial there. -/
theorem paper_conclusion_m2_level3_xi_ramification_pushforward :
    conclusion_m2_level3_xi_ramification_pushforward_klingen = (18, 0, 16) ∧
      conclusion_m2_level3_xi_ramification_pushforward_siegel = (24, 0, 12) ∧
      conclusion_m2_level3_xi_ramification_pushforward_flag = (96, 0, 64) := by
  rcases paper_conclusion_m2_level3_delta0_ramification_splitting with
    ⟨_, hProj3, _, hLag3, _, hFlag3, _, _⟩
  rcases paper_conclusion_m2_level3_xi_inertia_permutation_ramification with
    ⟨_, hXiProj, _, hXiLag, _, hXiFlag⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [conclusion_m2_level3_xi_ramification_pushforward_klingen, hProj3, hXiProj]
  · rw [conclusion_m2_level3_xi_ramification_pushforward_siegel, hLag3, hXiLag]
  · rw [conclusion_m2_level3_xi_ramification_pushforward_flag, hFlag3, hXiFlag]

end Omega.Conclusion
