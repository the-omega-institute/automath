import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinEscortLastbit
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Folding

/-- Concrete seed used to expose the already verified two-state asymptotic package in the escort
two-scale residual corollary. -/
def foldBinEscortTwoScaleResidualSeed : FoldBinTwoStateAsymptoticData := {}

/-- The scaled residual only remembers the last bit: `0 ↦ 1` and `1 ↦ φ⁻¹`. -/
noncomputable def foldBinEscortTwoScaleResidualAtom : Bool → ℝ
  | false => 1
  | true => Real.goldenRatio⁻¹

/-- The corresponding two-point law is the pushforward of the escort last-bit law. -/
noncomputable def foldBinEscortTwoScaleResidualPushforward (n : ℕ) : ℝ → ℚ
  | z =>
      if z = foldBinEscortTwoScaleResidualAtom false then
        foldBinEscortLastbitLaw n false
      else if z = foldBinEscortTwoScaleResidualAtom true then
        foldBinEscortLastbitLaw n true
      else
        0

private lemma foldBinEscortTwoScaleResidualAtom_ne :
    foldBinEscortTwoScaleResidualAtom true ≠ foldBinEscortTwoScaleResidualAtom false := by
  intro h
  have hlt : foldBinEscortTwoScaleResidualAtom true < foldBinEscortTwoScaleResidualAtom false := by
    dsimp [foldBinEscortTwoScaleResidualAtom]
    simpa using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  exact (ne_of_lt hlt) h

/-- Paper label: `cor:fold-bin-escort-two-scale-residual`. The already verified two-state
asymptotic uses the same two atoms `1` and `φ⁻¹`, and pushing the escort last-bit law forward
through that map yields the claimed two-point residual law. -/
theorem paper_fold_bin_escort_two_scale_residual :
    FoldBinTwoStateAsymptoticData.uniform_two_state_asymptotic foldBinEscortTwoScaleResidualSeed ∧
      (∀ b, foldBinEscortTwoScaleResidualAtom b = foldBinTwoStateWeight b) ∧
      (∀ n, 0 < n →
        foldBinEscortTwoScaleResidualPushforward n 1 = 1 / 3 ∧
          foldBinEscortTwoScaleResidualPushforward n Real.goldenRatio⁻¹ = 2 / 3 ∧
          foldBinEscortTwoScaleResidualPushforward n 1 +
            foldBinEscortTwoScaleResidualPushforward n Real.goldenRatio⁻¹ = 1) := by
  refine ⟨paper_fold_bin_two_state_asymptotic foldBinEscortTwoScaleResidualSeed, ?_, ?_⟩
  · intro b
    cases b <;> simp [foldBinEscortTwoScaleResidualAtom, foldBinTwoStateWeight]
  · intro n hn
    rcases (paper_fold_bin_escort_lastbit).1 n hn with ⟨h0, h1, hsum⟩
    have hphi_ne_one : (Real.goldenRatio⁻¹ : ℝ) ≠ 1 := by
      intro h
      exact foldBinEscortTwoScaleResidualAtom_ne (by
        simpa [foldBinEscortTwoScaleResidualAtom] using h)
    have hphi_ne_false : Real.goldenRatio⁻¹ ≠ foldBinEscortTwoScaleResidualAtom false := by
      simpa [foldBinEscortTwoScaleResidualAtom] using hphi_ne_one
    have hphi_eq_true : Real.goldenRatio⁻¹ = foldBinEscortTwoScaleResidualAtom true := by
      rfl
    refine ⟨?_, ?_, ?_⟩
    · simp [foldBinEscortTwoScaleResidualPushforward, foldBinEscortTwoScaleResidualAtom,
        h0]
    · unfold foldBinEscortTwoScaleResidualPushforward
      change
        (if Real.goldenRatio⁻¹ = foldBinEscortTwoScaleResidualAtom false then
          foldBinEscortLastbitLaw n false
        else if Real.goldenRatio⁻¹ = foldBinEscortTwoScaleResidualAtom true then
          foldBinEscortLastbitLaw n true
        else 0) = 2 / 3
      rw [if_neg hphi_ne_false, if_pos hphi_eq_true, h1]
    · rw [show foldBinEscortTwoScaleResidualPushforward n 1 = 1 / 3 by
        simp [foldBinEscortTwoScaleResidualPushforward, foldBinEscortTwoScaleResidualAtom, h0]]
      rw [show foldBinEscortTwoScaleResidualPushforward n Real.goldenRatio⁻¹ = 2 / 3 by
        unfold foldBinEscortTwoScaleResidualPushforward
        change
          (if Real.goldenRatio⁻¹ = foldBinEscortTwoScaleResidualAtom false then
            foldBinEscortLastbitLaw n false
          else if Real.goldenRatio⁻¹ = foldBinEscortTwoScaleResidualAtom true then
            foldBinEscortLastbitLaw n true
          else 0) = 2 / 3
        rw [if_neg hphi_ne_false, if_pos hphi_eq_true, h1]]
      simpa [h0, h1] using hsum

end Omega.Folding
