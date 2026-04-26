import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40PositiveEntropyFreezing

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The logarithmic-cusp normal form written using the auxiliary coefficient `A = d / c`. -/
def killo_real_input_40_rate_logarithmic_cusp_a_form (I_sat A δ : ℝ) : ℝ :=
  I_sat + 2 * δ * Real.log δ + 2 * δ * Real.log (2 / A) - 2 * δ

/-- The same logarithmic-cusp normal form after substituting `A = d / c`. -/
def killo_real_input_40_rate_logarithmic_cusp_dc_form (I_sat c d δ : ℝ) : ℝ :=
  I_sat + 2 * δ * Real.log δ + 2 * δ * Real.log (2 * c / d) - 2 * δ

/-- Paper label: `thm:killo-real-input-40-rate-logarithmic-cusp`.
The endpoint entropy identity gives `I_sat = log (φ² / c)`, and after substituting `A = d / c`
the logarithmic-cusp expression rewrites from `log (2 / A)` to `log (2 c / d)`. -/
def killo_real_input_40_rate_logarithmic_cusp_statement : Prop :=
  ∀ c d δ : ℝ, 1 < c → 0 < d → 0 < δ →
    let A := d / c
    let I_sat := Real.log (Real.goldenRatio ^ 2 / c)
    0 < realInput40GroundEntropy c ∧
      I_sat = Real.log (Real.goldenRatio ^ 2) - realInput40GroundEntropy c ∧
      killo_real_input_40_rate_logarithmic_cusp_a_form I_sat A δ =
        killo_real_input_40_rate_logarithmic_cusp_dc_form I_sat c d δ

theorem paper_killo_real_input_40_rate_logarithmic_cusp :
    killo_real_input_40_rate_logarithmic_cusp_statement := by
  intro c d δ hc hd hδ
  dsimp
  have hfreeze := paper_killo_real_input_40_positive_entropy_freezing c hc
  refine ⟨hfreeze.1, hfreeze.2.2, ?_⟩
  unfold killo_real_input_40_rate_logarithmic_cusp_a_form
    killo_real_input_40_rate_logarithmic_cusp_dc_form
  have hc0 : c ≠ 0 := ne_of_gt (lt_trans zero_lt_one hc)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hA : 2 / (d / c) = 2 * c / d := by
    field_simp [hc0, hd0]
  rw [hA]

end

end Omega.SyncKernelWeighted
