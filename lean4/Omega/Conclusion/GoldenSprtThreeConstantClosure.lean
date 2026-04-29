import Omega.Conclusion.GoldenSprtDeltaClosure

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-golden-sprt-three-constant-closure`. -/
theorem paper_conclusion_golden_sprt_three_constant_closure (T : ℝ) :
    ∃ posteriorScale timeScale infoScale : ℝ,
      posteriorScale = Real.goldenRatio ^ T ∧
        timeScale = 2 * Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)) ∧
          infoScale = Real.goldenRatio ^ (-(6 : ℝ)) ∧
            goldenSprtErrorPhi T = (1 + posteriorScale)⁻¹ := by
  refine ⟨Real.goldenRatio ^ T,
    2 * Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)),
    goldenSprtEtaSDPI, rfl, rfl, ?_, ?_⟩
  · rfl
  · simp [goldenSprtErrorPhi]

end Omega.Conclusion
