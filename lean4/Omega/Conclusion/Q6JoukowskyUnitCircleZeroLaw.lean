import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The normalized adjacency spectrum of `Q₆`, namely the eigenvalues of `(1 / 3) A(Q₆)`. -/
def conclusion_q6_joukowsky_unit_circle_zero_law_normalizedSpectrum : Finset ℝ :=
  {-(2 : ℝ), -(4 : ℝ) / 3, -(2 : ℝ) / 3, 0, (2 : ℝ) / 3, (4 : ℝ) / 3, 2}

/-- The quadratic factor corresponding to a normalized spectral value `μ`. -/
def conclusion_q6_joukowsky_unit_circle_zero_law_quadratic (μ : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 - (μ : ℂ) * z + 1

private lemma conclusion_q6_joukowsky_unit_circle_zero_law_spectrum_bound {μ : ℝ}
    (hμ :
      μ ∈ conclusion_q6_joukowsky_unit_circle_zero_law_normalizedSpectrum) :
    μ ^ 2 ≤ 4 := by
  simp [conclusion_q6_joukowsky_unit_circle_zero_law_normalizedSpectrum] at hμ
  rcases hμ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma conclusion_q6_joukowsky_unit_circle_zero_law_quadratic_abs_one {μ : ℝ}
    (hdisc : μ ^ 2 ≤ 4) {z : ℂ}
    (hz : conclusion_q6_joukowsky_unit_circle_zero_law_quadratic μ z = 0) :
    ‖z‖ = 1 := by
  have hre : z.re ^ 2 - z.im ^ 2 - μ * z.re + 1 = 0 := by
    have h := congrArg Complex.re hz
    simp [conclusion_q6_joukowsky_unit_circle_zero_law_quadratic, pow_two] at h
    linarith
  have him : z.im * (2 * z.re - μ) = 0 := by
    have h := congrArg Complex.im hz
    simp [conclusion_q6_joukowsky_unit_circle_zero_law_quadratic, pow_two] at h
    linarith
  have hdisc' : μ ^ 2 - 4 ≤ 0 := by
    linarith
  have hnormsq_complex : Complex.normSq z = 1 := by
    by_cases hy : z.im = 0
    · have hreal : z.re ^ 2 - μ * z.re + 1 = 0 := by
        simpa [hy] using hre
      have hsquare : (2 * z.re - μ) ^ 2 = μ ^ 2 - 4 := by
        nlinarith [hreal]
      have hzero : (2 * z.re - μ) ^ 2 = 0 := by
        nlinarith [sq_nonneg (2 * z.re - μ), hsquare, hdisc']
      have hre_eq : z.re = μ / 2 := by
        nlinarith
      have hmu_sq : μ ^ 2 = 4 := by
        nlinarith [hsquare, hzero]
      have hreal_sq : z.re ^ 2 = 1 := by
        nlinarith [hre_eq, hmu_sq]
      simpa [Complex.normSq_apply, hy, pow_two] using hreal_sq
    · have him_ne : z.im ≠ 0 := hy
      have hlin : 2 * z.re - μ = 0 := by
        rcases mul_eq_zero.mp him with him_zero | hlin
        · exact (him_ne him_zero).elim
        · exact hlin
      have hre_eq : z.re = μ / 2 := by
        nlinarith
      have hmu : μ = 2 * z.re := by
        nlinarith [hlin]
      have hsum : z.re ^ 2 + z.im ^ 2 = 1 := by
        rw [hmu] at hre
        nlinarith [hre]
      simpa [Complex.normSq_apply, pow_two] using hsum
  have hnormsq : ‖z‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormsq_complex
  have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith [hnormsq, hnorm_nonneg]

/-- Paper label: `prop:conclusion-q6-joukowsky-unit-circle-zero-law`. Every quadratic factor
`z² - μ z + 1` attached to the normalized `Q₆` adjacency spectrum has all of its roots on the unit
circle, so every zero in the Joukowsky factorization satisfies `|z| = 1`. -/
theorem paper_conclusion_q6_joukowsky_unit_circle_zero_law {μ : ℝ}
    (hμ : μ ∈ conclusion_q6_joukowsky_unit_circle_zero_law_normalizedSpectrum) {z : ℂ}
    (hz : conclusion_q6_joukowsky_unit_circle_zero_law_quadratic μ z = 0) :
    ‖z‖ = 1 := by
  exact conclusion_q6_joukowsky_unit_circle_zero_law_quadratic_abs_one
    (conclusion_q6_joukowsky_unit_circle_zero_law_spectrum_bound hμ) hz

end

end Omega.Conclusion
