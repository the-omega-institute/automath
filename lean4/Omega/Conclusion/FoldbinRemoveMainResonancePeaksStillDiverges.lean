import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence
import Omega.Conclusion.FoldSinglepairVisibleObstructions

namespace Omega.Conclusion

/-- The scaled collision excess `F_{m+2} Col_m - 1`. -/
def foldbinScaledCollisionExcess (Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  (Nat.fib (m + 2) : ℝ) * Col m - 1

/-- The two main Fibonacci resonance peaks contribute the bounded constant `2 C_φ²`. -/
def foldbinMainResonanceContribution : ℝ :=
  2 * singlepairResonanceConstant ^ (2 : ℕ)

/-- The residual collision excess after removing the two main resonance peaks. -/
def foldbinResidualCollisionExcess (Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  foldbinScaledCollisionExcess Col m - foldbinMainResonanceContribution

/-- Paper-facing proposition for removing the two main resonance peaks. -/
abbrev ConclusionFoldbinRemoveMainResonancePeaksStillDiverges : Prop :=
  ∀ Col : ℕ → ℝ,
    NatDivergesToInfinity (foldbinScaledCollisionExcess Col) →
      NatDivergesToInfinity (foldbinResidualCollisionExcess Col) ∧
        foldbinMainResonanceContribution = 2 * singlepairResonanceConstant ^ (2 : ℕ)

lemma foldbinMainResonanceContribution_eq_two :
    foldbinMainResonanceContribution = 2 := by
  simp [foldbinMainResonanceContribution, singlepairResonanceConstant]

lemma foldbinResidual_diverges_of_scaled_diverges (Col : ℕ → ℝ)
    (hdiv : NatDivergesToInfinity (foldbinScaledCollisionExcess Col)) :
    NatDivergesToInfinity (foldbinResidualCollisionExcess Col) := by
  intro K
  obtain ⟨m, hm⟩ := hdiv (K + 2)
  refine ⟨m, ?_⟩
  have hm' : ((K : ℝ) + 2 : ℝ) ≤ foldbinScaledCollisionExcess Col m := by
    simpa [Nat.cast_add] using hm
  unfold foldbinResidualCollisionExcess
  rw [foldbinMainResonanceContribution_eq_two]
  linarith

/-- Paper label: `prop:conclusion-foldbin-remove-main-resonance-peaks-still-diverges`.
Subtracting the bounded contribution of the two main Fibonacci resonance peaks changes the scaled
collision excess by the constant `2 C_φ² = 2`, so divergence to `+∞` persists. -/
theorem paper_conclusion_foldbin_remove_main_resonance_peaks_still_diverges :
    ConclusionFoldbinRemoveMainResonancePeaksStillDiverges := by
  intro Col hdiv
  refine ⟨foldbinResidual_diverges_of_scaled_diverges Col hdiv, rfl⟩

end Omega.Conclusion
