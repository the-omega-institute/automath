import Mathlib.Tactic

namespace Omega.Conclusion

/-- The quartic local Legendre jet used to compare left and right small deviations around the
typical density `μ₀`. The cubic term is the first asymmetric contribution. -/
noncomputable def realInput40LocalCramerJet (σ κ₃ κ₄ δ : ℝ) : ℝ :=
  δ ^ 2 / (2 * σ ^ 2) - (κ₃ / (6 * σ ^ 6)) * δ ^ 3 +
    ((3 * κ₃ ^ 2 - σ ^ 2 * κ₄) / (24 * σ ^ 10)) * δ ^ 4

/-- The odd part of the local Legendre jet is exactly the cubic asymmetry term. -/
theorem realInput40LocalCramerJet_difference (σ κ₃ κ₄ δ : ℝ) :
    realInput40LocalCramerJet σ κ₃ κ₄ δ - realInput40LocalCramerJet σ κ₃ κ₄ (-δ) =
      -(κ₃ / (3 * σ ^ 6)) * δ ^ 3 := by
  unfold realInput40LocalCramerJet
  ring

/-- If `κ₃ < 0`, then the cubic asymmetry makes the right tail locally more costly than the left
tail for every sufficiently small positive deviation already at the jet level. -/
theorem paper_conclusion_realinput40_local_cramer_right_tail_more_costly_package
    {σ κ₃ κ₄ δ : ℝ} (hσ : 0 < σ) (hκ₃ : κ₃ < 0) (hδ : 0 < δ) :
    realInput40LocalCramerJet σ κ₃ κ₄ δ - realInput40LocalCramerJet σ κ₃ κ₄ (-δ) =
      -(κ₃ / (3 * σ ^ 6)) * δ ^ 3 ∧
      0 <
        realInput40LocalCramerJet σ κ₃ κ₄ δ - realInput40LocalCramerJet σ κ₃ κ₄ (-δ) := by
  have hdiff := realInput40LocalCramerJet_difference σ κ₃ κ₄ δ
  have hcoeff_neg : κ₃ / (3 * σ ^ 6) < 0 := by
    have hden : 0 < 3 * σ ^ 6 := by positivity
    exact div_neg_of_neg_of_pos hκ₃ hden
  have hcoeff_pos : 0 < -(κ₃ / (3 * σ ^ 6)) := by linarith
  have hδ3 : 0 < δ ^ 3 := by positivity
  refine ⟨hdiff, ?_⟩
  rw [hdiff]
  nlinarith

/-- Paper label wrapper for the local right-tail asymmetry corollary.
    cor:conclusion-realinput40-local-cramer-right-tail-more-costly -/
def paper_conclusion_realinput40_local_cramer_right_tail_more_costly : Prop := by
  exact
    ∀ {σ κ₃ κ₄ δ : ℝ}, 0 < σ → κ₃ < 0 → 0 < δ →
      realInput40LocalCramerJet σ κ₃ κ₄ δ - realInput40LocalCramerJet σ κ₃ κ₄ (-δ) =
        -(κ₃ / (3 * σ ^ 6)) * δ ^ 3 ∧
        0 <
          realInput40LocalCramerJet σ κ₃ κ₄ δ - realInput40LocalCramerJet σ κ₃ κ₄ (-δ)

end Omega.Conclusion
