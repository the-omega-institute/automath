import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-pushforward-exact-size-bias`. -/
theorem paper_conclusion_binfold_pushforward_exact_size_bias :
    let φ : ℝ := Real.goldenRatio
    let EY : ℝ := (1 / φ) + (1 / φ ^ 3)
    EY = Real.sqrt 5 / φ ^ 2 ∧
      (1 / φ) / EY = φ / Real.sqrt 5 ∧
        (1 / φ ^ 3) / EY = 1 / (φ * Real.sqrt 5) := by
  dsimp
  set φ : ℝ := Real.goldenRatio
  set EY : ℝ := 1 / φ + 1 / φ ^ 3
  have hφ_ne : φ ≠ 0 := by
    simpa [φ] using Real.goldenRatio_ne_zero
  have hφ_sq : φ ^ 2 = φ + 1 := by
    simp [φ, Real.goldenRatio_sq]
  have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
    have hφ_def : φ = (1 + Real.sqrt 5) / 2 := by
      simp [φ, Real.goldenRatio]
    nlinarith
  have hsqrt_ne : Real.sqrt 5 ≠ 0 := by positivity
  have hEY : EY = Real.sqrt 5 / φ ^ 2 := by
    dsimp [EY]
    field_simp [hφ_ne]
    nlinarith [hφ_sq, hsqrt]
  refine ⟨hEY, ?_, ?_⟩
  · rw [hEY]
    field_simp [hφ_ne, hsqrt_ne]
  · rw [hEY]
    field_simp [hφ_ne, hsqrt_ne]

end Omega.Conclusion
