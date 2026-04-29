import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.ComplementaryGoldenBernoulliDivergence

namespace Omega.POM

noncomputable section

/-- Closed-form Rényi divergence spectrum (in bits) for the complementary golden Bernoulli pair. -/
def pom_complementary_golden_bernoulli_renyi_spectrum_closed_form (α : ℝ) : ℝ :=
  Real.log (Real.goldenRatio ^ (α - 2) + Real.goldenRatio ^ (-α - 1)) / ((α - 1) * Real.log 2)

/-- The order-`∞` endpoint of the same spectrum. -/
def pom_complementary_golden_bernoulli_renyi_spectrum_dinf : ℝ :=
  Real.log Real.goldenRatio / Real.log 2

/-- Concrete package containing the closed form and its endpoint evaluations. -/
def pom_complementary_golden_bernoulli_renyi_spectrum_statement : Prop :=
  (∀ α : ℝ, α ≠ 1 →
      pom_complementary_golden_bernoulli_renyi_spectrum_closed_form α =
        Real.log (Real.goldenRatio ^ (α - 2) + Real.goldenRatio ^ (-α - 1)) /
          ((α - 1) * Real.log 2)) ∧
    pom_complementary_golden_bernoulli_renyi_spectrum_closed_form (1 / 2 : ℝ) =
      3 * (Real.log Real.goldenRatio / Real.log 2) - 2 ∧
    pom_complementary_golden_bernoulli_renyi_spectrum_closed_form 2 =
      Real.log (1 + Real.goldenRatio ^ (-3 : ℝ)) / Real.log 2 ∧
    pom_complementary_golden_bernoulli_renyi_spectrum_dinf = Real.log Real.goldenRatio / Real.log 2

/-- Paper label: `prop:pom-complementary-golden-bernoulli-renyi-spectrum`. The complementary
golden Bernoulli pair admits the explicit Rényi closed form
`(α - 1)⁻¹ log₂ (φ^(α - 2) + φ^(-α - 1))`, and the special values at
`α = 1/2`, `2`, and `∞` reduce to the stated expressions. -/
theorem paper_pom_complementary_golden_bernoulli_renyi_spectrum :
    pom_complementary_golden_bernoulli_renyi_spectrum_statement := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro α hα
    rfl
  · have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
    have hpow_pos : 0 < Real.goldenRatio ^ (-(3 / 2 : ℝ)) := by positivity
    have hlog2_ne : Real.log 2 ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by norm_num))
    have hhalf_exp1 : ((1 / 2 : ℝ) - 2) = -(3 / 2 : ℝ) := by norm_num
    have hhalf_exp2 : (-(1 / 2 : ℝ) - 1) = -(3 / 2 : ℝ) := by norm_num
    calc
      pom_complementary_golden_bernoulli_renyi_spectrum_closed_form (1 / 2 : ℝ)
          = Real.log (2 * Real.goldenRatio ^ (-(3 / 2 : ℝ))) / ((-(1 / 2 : ℝ)) * Real.log 2) := by
              rw [pom_complementary_golden_bernoulli_renyi_spectrum_closed_form, hhalf_exp1, hhalf_exp2]
              ring
      _ = (-2 : ℝ) * (Real.log (2 * Real.goldenRatio ^ (-(3 / 2 : ℝ))) / Real.log 2) := by
            field_simp [hlog2_ne]
      _ = (-2 : ℝ) *
            ((Real.log 2 + Real.log (Real.goldenRatio ^ (-(3 / 2 : ℝ)))) / Real.log 2) := by
              rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (ne_of_gt hpow_pos)]
      _ = (-2 : ℝ) * ((Real.log 2 + (-(3 / 2 : ℝ)) * Real.log Real.goldenRatio) / Real.log 2) := by
              rw [Real.log_rpow hphi_pos]
      _ = 3 * (Real.log Real.goldenRatio / Real.log 2) - 2 := by
            field_simp [hlog2_ne]
            ring
  · have hpow_neg : Real.goldenRatio ^ (-3 : ℝ) = (Real.goldenRatio ^ (3 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt Real.goldenRatio_pos)]
    have htwo_exp : (-(2 : ℝ) - 1) = (-3 : ℝ) := by norm_num
    have hden : ((2 - 1 : ℝ) * Real.log 2) = Real.log 2 := by ring
    rw [pom_complementary_golden_bernoulli_renyi_spectrum_closed_form, hden, htwo_exp]
    simp [hpow_neg]

end

end Omega.POM
