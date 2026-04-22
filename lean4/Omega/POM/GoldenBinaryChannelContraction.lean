import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.POM

/-- The `B = 1` output probability under the `+` input. -/
noncomputable def goldenBinaryPlusProb : ℝ :=
  Real.goldenRatio⁻¹

/-- The `B = 1` output probability under the `-` input. -/
noncomputable def goldenBinaryMinusProb : ℝ :=
  (Real.goldenRatio⁻¹) ^ 2

/-- The Bernoulli parameter gap controlling both TV contraction and correlation. -/
noncomputable def goldenBinaryGap : ℝ :=
  goldenBinaryPlusProb - goldenBinaryMinusProb

/-- Dobrushin contraction constant for the golden binary channel. -/
noncomputable def goldenBinaryTvContractionConstant : ℝ :=
  |goldenBinaryGap|

/-- For this `2 × 2` channel the maximal correlation is the same scalar. -/
noncomputable def goldenBinaryHgrMaxCorrelation : ℝ :=
  goldenBinaryTvContractionConstant

/-- Output Bernoulli parameter induced by an input prior `a` on the `+` state. -/
noncomputable def goldenBinaryOutputParameter (a : ℝ) : ℝ :=
  goldenBinaryMinusProb + a * goldenBinaryGap

/-- The optimal SDPI constant is the square of the maximal correlation. -/
noncomputable def goldenBinarySdpiOptimalConstant : ℝ :=
  goldenBinaryHgrMaxCorrelation ^ 2

private lemma golden_inv_eq_sub_one : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]

private lemma golden_gap_eq_inv_cube : goldenBinaryGap = (Real.goldenRatio⁻¹) ^ 3 := by
  let x : ℝ := Real.goldenRatio⁻¹
  have hx : x = Real.goldenRatio - 1 := golden_inv_eq_sub_one
  have hx_sq : x ^ 2 = 1 - x := by
    nlinarith [Real.goldenRatio_sq, hx]
  calc
    goldenBinaryGap = x - x ^ 2 := by simp [goldenBinaryGap, goldenBinaryPlusProb,
      goldenBinaryMinusProb, x]
    _ = x ^ 3 := by
      calc
        x - x ^ 2 = x * (1 - x) := by ring
        _ = x * x ^ 2 := by rw [hx_sq]
        _ = x ^ 3 := by ring
    _ = (Real.goldenRatio⁻¹) ^ 3 := by simp [x]

private lemma golden_gap_nonneg : 0 ≤ goldenBinaryGap := by
  rw [golden_gap_eq_inv_cube]
  positivity

/-- Paper label: `thm:pom-golden-binary-channel-contraction`.
For the golden complementary binary kernel with probabilities `φ⁻¹` and `φ⁻²`, the TV
contraction constant and the maximal correlation both collapse to `φ⁻³`, the Bernoulli output
parameter scales exactly by the same factor, and the SDPI constant is the square `φ⁻⁶`. -/
theorem paper_pom_golden_binary_channel_contraction :
    goldenBinaryTvContractionConstant = (Real.goldenRatio⁻¹) ^ 3 ∧
      goldenBinaryHgrMaxCorrelation = (Real.goldenRatio⁻¹) ^ 3 ∧
      (∀ a b : ℝ,
        |goldenBinaryOutputParameter a - goldenBinaryOutputParameter b| =
          (Real.goldenRatio⁻¹) ^ 3 * |a - b|) ∧
      goldenBinarySdpiOptimalConstant = (Real.goldenRatio⁻¹) ^ 6 := by
  have htv : goldenBinaryTvContractionConstant = (Real.goldenRatio⁻¹) ^ 3 := by
    rw [goldenBinaryTvContractionConstant, abs_of_nonneg golden_gap_nonneg, golden_gap_eq_inv_cube]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact htv
  · simpa [goldenBinaryHgrMaxCorrelation] using htv
  · intro a b
    have hparam :
        goldenBinaryOutputParameter a - goldenBinaryOutputParameter b =
          a * goldenBinaryGap - b * goldenBinaryGap := by
      simp [goldenBinaryOutputParameter]
    calc
      |goldenBinaryOutputParameter a - goldenBinaryOutputParameter b|
          = |a * goldenBinaryGap - b * goldenBinaryGap| := by rw [hparam]
      _ = |(a - b) * goldenBinaryGap| := by
            congr 1
            ring
      _ = |a - b| * |goldenBinaryGap| := by rw [abs_mul]
      _ = |a - b| * (Real.goldenRatio⁻¹) ^ 3 := by
            rw [abs_of_nonneg golden_gap_nonneg, golden_gap_eq_inv_cube]
      _ = (Real.goldenRatio⁻¹) ^ 3 * |a - b| := by ring
  · calc
      goldenBinarySdpiOptimalConstant = (goldenBinaryTvContractionConstant) ^ 2 := by
        simp [goldenBinarySdpiOptimalConstant, goldenBinaryHgrMaxCorrelation]
      _ = ((Real.goldenRatio⁻¹) ^ 3) ^ 2 := by
        rw [htv]
      _ = (Real.goldenRatio⁻¹) ^ (3 * 2) := by
        simpa using (pow_mul (Real.goldenRatio⁻¹) 3 2).symm
      _ = (Real.goldenRatio⁻¹) ^ 6 := by
        norm_num

end Omega.POM
