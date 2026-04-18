import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The contraction constant of the golden complementary binary channel. -/
noncomputable def goldenSprtDelta : ℝ := Real.goldenRatio ^ (-3 : ℝ)

/-- The maximal correlation contraction equals the same golden constant. -/
noncomputable def goldenSprtRhoMax : ℝ := Real.goldenRatio ^ (-3 : ℝ)

/-- The mutual-information SDPI constant is the square of the TV contraction. -/
noncomputable def goldenSprtEtaSDPI : ℝ := Real.goldenRatio ^ (-6 : ℝ)

/-- Closed-form symmetric SPRT error curve in the `φ` parametrization. -/
noncomputable def goldenSprtErrorPhi (T : ℝ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ T)

/-- Closed-form symmetric SPRT expected time in the `φ` parametrization. -/
noncomputable def goldenSprtTimePhi (T : ℝ) : ℝ :=
  Real.goldenRatio ^ (3 : ℝ) * T *
    ((Real.goldenRatio ^ T - 1) / (Real.goldenRatio ^ T + 1))

/-- Reparameterized symmetric SPRT error curve written only in the contraction constant `δ`. -/
noncomputable def goldenSprtErrorDelta (T : ℝ) : ℝ :=
  1 / (1 + goldenSprtDelta ^ (-(T / 3)))

/-- Reparameterized symmetric SPRT expected time written only in the contraction constant `δ`. -/
noncomputable def goldenSprtTimeDelta (T : ℝ) : ℝ :=
  goldenSprtDelta ^ (-1 : ℝ) * T *
    ((goldenSprtDelta ^ (-(T / 3)) - 1) / (goldenSprtDelta ^ (-(T / 3)) + 1))

/-- The golden contraction constant simultaneously controls TV/ρ-max contraction, SDPI, and the
symmetric SPRT risk/time curve after rewriting the `φ` formulas in terms of `δ = φ^{-3}`.
    thm:conclusion-golden-sprt-delta-closure -/
theorem paper_conclusion_golden_sprt_delta_closure (T : ℝ) :
    goldenSprtDelta = goldenSprtRhoMax ∧
    goldenSprtEtaSDPI = goldenSprtDelta ^ (2 : ℝ) ∧
    goldenSprtErrorPhi T = goldenSprtErrorDelta T ∧
    goldenSprtTimePhi T = goldenSprtTimeDelta T := by
  have hφ : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hdeltaLift : goldenSprtDelta ^ (-(T / 3)) = Real.goldenRatio ^ T := by
    unfold goldenSprtDelta
    calc
      (Real.goldenRatio ^ (-3 : ℝ)) ^ (-(T / 3))
          = Real.goldenRatio ^ ((-3 : ℝ) * (-(T / 3))) := by
              symm
              exact Real.rpow_mul hφ.le (-3 : ℝ) (-(T / 3))
      _ = Real.goldenRatio ^ T := by ring_nf
  have hdeltaInv : goldenSprtDelta ^ (-1 : ℝ) = Real.goldenRatio ^ (3 : ℝ) := by
    unfold goldenSprtDelta
    calc
      (Real.goldenRatio ^ (-3 : ℝ)) ^ (-1 : ℝ) = Real.goldenRatio ^ ((-3 : ℝ) * (-1 : ℝ)) := by
        symm
        exact Real.rpow_mul hφ.le (-3 : ℝ) (-1 : ℝ)
      _ = Real.goldenRatio ^ (3 : ℝ) := by ring_nf
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold goldenSprtEtaSDPI goldenSprtDelta
    calc
      Real.goldenRatio ^ (-6 : ℝ) = Real.goldenRatio ^ ((-3 : ℝ) * (2 : ℝ)) := by ring_nf
      _ = (Real.goldenRatio ^ (-3 : ℝ)) ^ (2 : ℝ) := by
        exact Real.rpow_mul hφ.le (-3 : ℝ) (2 : ℝ)
  · rw [goldenSprtErrorPhi, goldenSprtErrorDelta, hdeltaLift]
  · rw [goldenSprtTimePhi, goldenSprtTimeDelta, hdeltaInv, hdeltaLift]

end Omega.Conclusion
