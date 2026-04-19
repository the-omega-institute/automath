import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

/-- A concrete Perron branch with matching large-`u` and small-`u` asymptotics after the change of
variables `u = exp θ`. -/
noncomputable def gaugeAnomalyGcPerronRoot (θ : ℝ) : ℝ :=
  Real.exp θ + 1 + Real.exp (-θ)

/-- Logarithmic GC-defect after removing the dominant far-field contribution `|θ|`. -/
noncomputable def gaugeAnomalyGcFarfieldDefect (θ : ℝ) : ℝ :=
  Real.log (gaugeAnomalyGcPerronRoot θ) - |θ|

private lemma gaugeAnomalyGcPerronRoot_pos (θ : ℝ) :
    0 < gaugeAnomalyGcPerronRoot θ := by
  unfold gaugeAnomalyGcPerronRoot
  positivity

private lemma gaugeAnomalyGcPerronRoot_factor_pos (θ : ℝ) :
    0 < 1 + Real.exp (-θ) + Real.exp (-(2 * θ)) := by
  positivity

private lemma gaugeAnomalyGcPerronRoot_factor_neg (θ : ℝ) :
    0 < 1 + Real.exp θ + Real.exp (2 * θ) := by
  positivity

private lemma gaugeAnomalyGcPerronRoot_factorization_pos (θ : ℝ) :
    gaugeAnomalyGcPerronRoot θ =
      Real.exp θ * (1 + Real.exp (-θ) + Real.exp (-(2 * θ))) := by
  have hmul₁ : Real.exp θ * Real.exp (-θ) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hmul₂ : Real.exp θ * Real.exp (-(2 * θ)) = Real.exp (-θ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    gaugeAnomalyGcPerronRoot θ = Real.exp θ + 1 + Real.exp (-θ) := rfl
    _ = Real.exp θ + Real.exp θ * Real.exp (-θ) + Real.exp θ * Real.exp (-(2 * θ)) := by
      rw [hmul₁, hmul₂]
    _ = Real.exp θ * (1 + Real.exp (-θ) + Real.exp (-(2 * θ))) := by ring

private lemma gaugeAnomalyGcPerronRoot_factorization_neg (θ : ℝ) :
    gaugeAnomalyGcPerronRoot θ =
      Real.exp (-θ) * (1 + Real.exp θ + Real.exp (2 * θ)) := by
  have hmul₁ : Real.exp (-θ) * Real.exp θ = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hmul₂ : Real.exp (-θ) * Real.exp (2 * θ) = Real.exp θ := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    gaugeAnomalyGcPerronRoot θ = Real.exp (-θ) + 1 + Real.exp θ := by
      unfold gaugeAnomalyGcPerronRoot
      ring_nf
    _ = Real.exp (-θ) * Real.exp (2 * θ) + Real.exp (-θ) * Real.exp θ + Real.exp (-θ) := by
      rw [hmul₁, hmul₂]
      ring
    _ = Real.exp (-θ) * (1 + Real.exp θ + Real.exp (2 * θ)) := by ring

private lemma gaugeAnomalyGcFarfieldDefect_pos (θ : ℝ) (hθ : 0 ≤ θ) :
    gaugeAnomalyGcFarfieldDefect θ =
      Real.log (1 + Real.exp (-θ) + Real.exp (-(2 * θ))) := by
  rw [gaugeAnomalyGcFarfieldDefect, abs_of_nonneg hθ, gaugeAnomalyGcPerronRoot_factorization_pos]
  rw [Real.log_mul (Real.exp_ne_zero θ)
    (ne_of_gt (gaugeAnomalyGcPerronRoot_factor_pos θ)), Real.log_exp]
  ring

private lemma gaugeAnomalyGcFarfieldDefect_neg (θ : ℝ) (hθ : θ ≤ 0) :
    gaugeAnomalyGcFarfieldDefect θ =
      Real.log (1 + Real.exp θ + Real.exp (2 * θ)) := by
  rw [gaugeAnomalyGcFarfieldDefect, abs_of_nonpos hθ, gaugeAnomalyGcPerronRoot_factorization_neg]
  rw [Real.log_mul (Real.exp_ne_zero (-θ))
    (ne_of_gt (gaugeAnomalyGcPerronRoot_factor_neg θ)), Real.log_exp]
  ring

/-- After the substitution `u = exp θ`, the Perron branch has exact first-order far-field
logarithmic expansions on the `θ → +∞` and `θ → -∞` sides. At the golden bias
`θ = log φ`, the defect collapses to `log 2`.
    prop:fold-gauge-anomaly-gc-defect-farfield-expansion -/
theorem paper_fold_gauge_anomaly_gc_defect_farfield_expansion :
    (∀ θ : ℝ, 0 ≤ θ →
      gaugeAnomalyGcFarfieldDefect θ =
        Real.log (1 + Real.exp (-θ) + Real.exp (-(2 * θ)))) ∧
      (∀ θ : ℝ, θ ≤ 0 →
        gaugeAnomalyGcFarfieldDefect θ =
          Real.log (1 + Real.exp θ + Real.exp (2 * θ))) ∧
      gaugeAnomalyGcFarfieldDefect (Real.log Real.goldenRatio) = Real.log 2 := by
  refine ⟨gaugeAnomalyGcFarfieldDefect_pos, gaugeAnomalyGcFarfieldDefect_neg, ?_⟩
  have hlogphi : 0 ≤ Real.log Real.goldenRatio := by
    exact le_of_lt (Real.log_pos Real.one_lt_goldenRatio)
  rw [gaugeAnomalyGcFarfieldDefect_pos _ hlogphi]
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hexp₁ : Real.exp (-Real.log Real.goldenRatio) = Real.goldenRatio⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hphi_pos]
  have hexp₂ : Real.exp (-(2 * Real.log Real.goldenRatio)) = (Real.goldenRatio ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    have hsq :
        Real.exp (2 * Real.log Real.goldenRatio) = Real.goldenRatio ^ 2 := by
      calc
        Real.exp (2 * Real.log Real.goldenRatio)
            = Real.exp (Real.log Real.goldenRatio + Real.log Real.goldenRatio) := by
              congr 1
              ring
        _ = Real.exp (Real.log Real.goldenRatio) * Real.exp (Real.log Real.goldenRatio) := by
              rw [Real.exp_add]
        _ = Real.goldenRatio * Real.goldenRatio := by simpa [Real.exp_log hphi_pos]
        _ = Real.goldenRatio ^ 2 := by ring
    simpa using congrArg Inv.inv hsq
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsum : 1 + Real.goldenRatio⁻¹ + (Real.goldenRatio ^ 2)⁻¹ = 2 := by
    rw [Real.goldenRatio]
    have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
    have hroot_ne : (1 + Real.sqrt 5 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5]
    field_simp [hroot_ne]
    nlinarith [hsqrt5_sq]
  rw [hexp₁, hexp₂, hsum]

end Omega.Folding
