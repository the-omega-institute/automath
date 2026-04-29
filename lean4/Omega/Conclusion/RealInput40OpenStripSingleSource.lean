import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.RealInput40ZetaFactorization

namespace Omega.Conclusion

noncomputable section

/-- The open critical strip used by the real-input-40 single-source statement. -/
def conclusion_realinput40_open_strip_single_source_strip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The real quadratic factor coming from the sign-twisted Fibonacci block. -/
def conclusion_realinput40_open_strip_single_source_quadratic (z : ℝ) : ℝ :=
  1 + z - z ^ 2

/-- The same quadratic split into the two golden linear factors. -/
def conclusion_realinput40_open_strip_single_source_goldenFactors (z : ℝ) : ℝ :=
  (1 - Real.goldenRatio⁻¹ * z) * (1 + Real.goldenRatio * z)

/-- Concrete holomorphic/no-zero strip condition for the residual source. -/
def conclusion_realinput40_open_strip_single_source_holomorphicNoZero
    (H : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ H conclusion_realinput40_open_strip_single_source_strip ∧
    ∀ s ∈ conclusion_realinput40_open_strip_single_source_strip, H s ≠ 0

/-- A zeta function whose open-strip poles are sourced by a single displayed denominator. -/
def conclusion_realinput40_open_strip_single_source_statement
    (H zetaHat denominator : ℂ → ℂ) : Prop :=
  conclusion_realinput40_open_strip_single_source_holomorphicNoZero H ∧
    ∀ s ∈ conclusion_realinput40_open_strip_single_source_strip,
      denominator s ≠ 0 → zetaHat s = H s / denominator s

/-- Paper label: `thm:conclusion-realinput40-open-strip-single-source`. -/
theorem paper_conclusion_realinput40_open_strip_single_source :
    (∀ z : ℝ,
        conclusion_realinput40_open_strip_single_source_quadratic z =
          conclusion_realinput40_open_strip_single_source_goldenFactors z) ∧
      Omega.POM.realInput40DetFactorization ∧
      ∀ H zetaHat denominator : ℂ → ℂ,
        conclusion_realinput40_open_strip_single_source_holomorphicNoZero H →
          (∀ s ∈ conclusion_realinput40_open_strip_single_source_strip,
            denominator s ≠ 0 → zetaHat s = H s / denominator s) →
            conclusion_realinput40_open_strip_single_source_statement
              H zetaHat denominator := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    unfold conclusion_realinput40_open_strip_single_source_quadratic
      conclusion_realinput40_open_strip_single_source_goldenFactors
    have hinv_conj : (Real.goldenRatio⁻¹ : ℝ) = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    have hinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
      nlinarith [hinv_conj, Real.goldenRatio_add_goldenConj]
    rw [hinv]
    nlinarith [Real.goldenRatio_sq]
  · exact (Omega.POM.paper_pom_zeta_factorization_40).1
  · intro H zetaHat denominator hH hzeta
    exact ⟨hH, hzeta⟩

end

end Omega.Conclusion
