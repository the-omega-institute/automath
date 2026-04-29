import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyClt

namespace Omega.Folding

/-- The quadratic pressure expansion on the imaginary axis forced by the CLT variance
`σ_G² = 118 / 243`. -/
noncomputable def foldGaugeAnomalyPressureImaginaryAxis (t : ℝ) : ℝ :=
  -((((gaugeAnomalyVarianceConstant : Rat) : ℝ) / 2) * t ^ 2)

/-- The dominant root branch normalized so that `μ(0) = 2`. -/
noncomputable def foldGaugeAnomalyDominantRootBranch (t : ℝ) : ℝ :=
  2 * Real.exp (foldGaugeAnomalyPressureImaginaryAxis t)

/-- The large-`q` spectral-gap model obtained by substituting `t = 2π / q`. -/
noncomputable def foldGaugeAnomalyLargeQDelta (q : ℕ) : ℝ :=
  Real.exp (foldGaugeAnomalyPressureImaginaryAxis (2 * Real.pi / q))

/-- Paper label: `thm:fold-gauge-anomaly-large-q-delta`. -/
theorem paper_fold_gauge_anomaly_large_q_delta (normalizedPartialSums : ℕ → ℝ)
    (hclt : gaugeAnomalyCentralLimitLaw normalizedPartialSums) {q : ℕ} (hq : 0 < q) :
    foldGaugeAnomalyLargeQDelta q =
      foldGaugeAnomalyDominantRootBranch (2 * Real.pi / q) / 2 ∧
      foldGaugeAnomalyPressureImaginaryAxis (2 * Real.pi / q) =
        -(236 * Real.pi ^ 2) / (243 * q ^ 2) ∧
      foldGaugeAnomalyLargeQDelta q = Real.exp (-(236 * Real.pi ^ 2) / (243 * q ^ 2)) ∧
      0 < foldGaugeAnomalyLargeQDelta q := by
  have hPkg := paper_fold_gauge_anomaly_clt normalizedPartialSums hclt
  have hσ :
      (((gaugeAnomalyVarianceConstant : Rat) : ℝ)) = (118 : ℝ) / 243 := by
    norm_num [hPkg.2.1]
  have hqR : (q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq
  refine ⟨?_, ?_, ?_, Real.exp_pos _⟩
  · unfold foldGaugeAnomalyLargeQDelta foldGaugeAnomalyDominantRootBranch
    ring_nf
  · calc
      foldGaugeAnomalyPressureImaginaryAxis (2 * Real.pi / q)
          = -((((118 : ℝ) / 243) / 2) * (2 * Real.pi / q) ^ 2) := by
              rw [foldGaugeAnomalyPressureImaginaryAxis, hσ]
      _ = -(236 * Real.pi ^ 2) / (243 * q ^ 2) := by
            field_simp [hqR]
            ring
  · rw [foldGaugeAnomalyLargeQDelta]
    congr 1
    calc
      foldGaugeAnomalyPressureImaginaryAxis (2 * Real.pi / q)
          = -((((118 : ℝ) / 243) / 2) * (2 * Real.pi / q) ^ 2) := by
              rw [foldGaugeAnomalyPressureImaginaryAxis, hσ]
      _ = -(236 * Real.pi ^ 2) / (243 * q ^ 2) := by
            field_simp [hqR]
            ring

end Omega.Folding
