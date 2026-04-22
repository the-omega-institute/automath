import Mathlib
import Omega.Conclusion.PowerDivergenceSecondorderRecurrence

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `prop:conclusion-power-divergence-logconvex-dominant-ratio`. In the concrete
golden-ratio two-exponential model for the limiting power-divergence family, the spectrum is
strictly log-convex, the smaller and larger density-ratio roots are exactly `φ / √5` and
`φ² / √5`, and the larger one is the dominant ratio singled out by the model. -/
theorem paper_conclusion_power_divergence_logconvex_dominant_ratio :
    let D : PowerDivergenceSpectrumData :=
      { leftWeight := (Real.goldenRatio⁻¹) ^ 2
        rightWeight := Real.goldenRatio⁻¹
        leftRate := Real.log (Real.goldenRatio / Real.sqrt 5)
        rightRate := Real.log (Real.goldenRatio ^ 2 / Real.sqrt 5)
        hleftWeight := by positivity
        hrightWeight := by positivity
        hrate := by
          have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
          have hlt :
              Real.goldenRatio / Real.sqrt 5 < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
            have hφ : Real.goldenRatio < Real.goldenRatio ^ 2 := by
              nlinarith [Real.goldenRatio_sq]
            exact (div_lt_div_iff_of_pos_right hsqrt5_pos).2 hφ
          exact Real.log_lt_log (by positivity) hlt }
    D.explicitFormula ∧ D.strictLogConvex ∧
      D.leftRoot = Real.goldenRatio / Real.sqrt 5 ∧
      D.rightRoot = Real.goldenRatio ^ 2 / Real.sqrt 5 ∧
      D.leftRoot < D.rightRoot := by
  dsimp
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have hlt :
      Real.goldenRatio / Real.sqrt 5 < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
    have hφ : Real.goldenRatio < Real.goldenRatio ^ 2 := by
      nlinarith [Real.goldenRatio_sq]
    exact (div_lt_div_iff_of_pos_right hsqrt5_pos).2 hφ
  let D : PowerDivergenceSpectrumData :=
    { leftWeight := (Real.goldenRatio⁻¹) ^ 2
      rightWeight := Real.goldenRatio⁻¹
      leftRate := Real.log (Real.goldenRatio / Real.sqrt 5)
      rightRate := Real.log (Real.goldenRatio ^ 2 / Real.sqrt 5)
      hleftWeight := by positivity
      hrightWeight := by positivity
      hrate := by
        exact Real.log_lt_log (by positivity) hlt }
  have hpkg := paper_conclusion_power_divergence_secondorder_recurrence D
  refine ⟨hpkg.1, hpkg.2.2, ?_, ?_, ?_⟩
  · rw [PowerDivergenceSpectrumData.leftRoot]
    exact Real.exp_log (by positivity)
  · rw [PowerDivergenceSpectrumData.rightRoot]
    exact Real.exp_log (by positivity)
  · simpa [PowerDivergenceSpectrumData.leftRoot, PowerDivergenceSpectrumData.rightRoot] using
      (Real.log_lt_log (by positivity) hlt)

end

end Omega.Conclusion
