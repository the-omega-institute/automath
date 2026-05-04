import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction
import Omega.Conclusion.OddMaxfiberHiddenbitTristateCrystal

open Filter

namespace Omega.Conclusion

noncomputable section

/-- Conclusion-facing self-calibration package: the odd-window hidden-bit collision endpoint
converges to the golden constant, and substituting that endpoint into the already formalized
two-point hidden-bit formulas yields the low/high leakage constants `φ⁻²` and `φ⁻¹`. -/
def conclusion_maxfiber_hiddenbit_collision_selfcalibration_statement : Prop :=
  Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / (2 * Nat.fib (n + 3))) atTop
      (nhds ((1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3)) ∧
    ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 = Real.goldenRatio⁻¹) ∧
    ((1 / 2 : ℝ) - (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 = (Real.goldenRatio⁻¹ : ℝ) ^ 2) ∧
    binfoldTwoPointLimitMassHigh Real.goldenRatio 0 = Real.goldenRatio⁻¹ ∧
    binfoldTwoPointLimitMassLow Real.goldenRatio 0 = (Real.goldenRatio⁻¹ : ℝ) ^ 2 ∧
    binfoldTwoPointLimitMassLow Real.goldenRatio 0 +
      binfoldTwoPointLimitMassHigh Real.goldenRatio 0 = 1

/-- Paper label: `thm:conclusion-maxfiber-hiddenbit-collision-selfcalibration`. -/
theorem paper_conclusion_maxfiber_hiddenbit_collision_selfcalibration :
    conclusion_maxfiber_hiddenbit_collision_selfcalibration_statement := by
  rcases paper_conclusion_odd_maxfiber_hiddenbit_tristate_crystal 0 (1 / 2 : ℝ) (Or.inl rfl) with
    ⟨_, hDelta, hHighEndpoint, hLowEndpoint⟩
  rcases paper_conclusion_binfold_two_scalar_complete_reconstruction with
    ⟨_, _, _, _, _, hMassSum, hLaw⟩
  rcases hLaw 0 with ⟨hLow0, hHigh0⟩
  have hPhiSq : (Real.goldenRatio : ℝ) ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hPhiSqOne : (1 : ℝ) + Real.goldenRatio = Real.goldenRatio ^ 2 := by
    calc
      (1 : ℝ) + Real.goldenRatio = Real.goldenRatio + 1 := by ring
      _ = Real.goldenRatio ^ 2 := hPhiSq.symm
  have hPhiNe : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hHighMass : binfoldTwoPointLimitMassHigh Real.goldenRatio 0 = Real.goldenRatio⁻¹ := by
    rw [hHigh0]
    calc
      Real.goldenRatio ^ (0 + 1) / (1 + Real.goldenRatio ^ (0 + 1)) =
          Real.goldenRatio / (1 + Real.goldenRatio) := by
            simp [pow_one]
      _ = Real.goldenRatio / (Real.goldenRatio ^ 2) := by
            rw [hPhiSqOne]
      _ = Real.goldenRatio⁻¹ := by
            rw [pow_two]
            field_simp [hPhiNe]
  have hLowMass : binfoldTwoPointLimitMassLow Real.goldenRatio 0 = (Real.goldenRatio⁻¹ : ℝ) ^ 2 := by
    rw [hLow0]
    calc
      (1 : ℝ) / (1 + Real.goldenRatio ^ (0 + 1)) = 1 / (1 + Real.goldenRatio) := by
        simp [pow_one]
      _ = 1 / (Real.goldenRatio ^ 2) := by
        rw [hPhiSqOne]
      _ = (Real.goldenRatio⁻¹ : ℝ) ^ 2 := by
        rw [one_div, inv_pow]
  exact ⟨hDelta, hHighEndpoint, hLowEndpoint, hHighMass, hLowMass, hMassSum 0⟩

/-- Paper label: `cor:conclusion-maxfiber-gcd-determines-hiddenbit-entropy-class`. -/
theorem paper_conclusion_maxfiber_gcd_determines_hiddenbit_entropy_class (Phase : Type*)
    (gcdClass : Phase → ℕ) (hiddenEntropy : Phase → ℝ) (entropyOfGcd : ℕ → ℝ)
    (hclass : ∀ x, hiddenEntropy x = entropyOfGcd (gcdClass x)) :
    ∃ E : ℕ → ℝ, ∀ x, hiddenEntropy x = E (gcdClass x) := by
  exact ⟨entropyOfGcd, hclass⟩

end

end Omega.Conclusion
