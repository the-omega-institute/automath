import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The standard Cayley-angle parametrization of the unit circle, written in the `x = tan(θ/2)`
coordinate. -/
def unitCircleCayleyMap (x : ℝ) : ℂ :=
  Complex.mk (Real.cos (2 * Real.arctan x)) (Real.sin (2 * Real.arctan x))

/-- The phase embedding differs from the Cayley parametrization by the central factor `-1`. -/
def unitCirclePhaseEmbedding (x : ℝ) : ℂ :=
  Complex.mk (Real.cos (2 * Real.arctan x + Real.pi)) (Real.sin (2 * Real.arctan x + Real.pi))

/-- The Cayley angle as a function of the real coordinate `x`. -/
def cayleyAngle (x : ℝ) : ℝ :=
  Real.arctan x + Real.arctan x

/-- The normalized pullback density of Haar measure under `θ(x) = 2 arctan x`. -/
def cayleyHaarPullbackDensity (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (2 / (1 + x ^ 2))

/-- The standard Cauchy density. -/
def cauchyDensity (x : ℝ) : ℝ :=
  1 / (Real.pi * (1 + x ^ 2))

/-- Paper label: `cor:unit-circle-cayley-haar-forces-cauchy`.
The phase embedding is the Cayley parametrization multiplied by `-1`, the Jacobian of
`θ(x) = 2 arctan x` is `2 / (1 + x²)`, and the normalized Haar pullback is exactly the Cauchy
density. -/
theorem paper_unit_circle_cayley_haar_forces_cauchy (x : ℝ) :
    unitCirclePhaseEmbedding x = -unitCircleCayleyMap x ∧
      HasDerivAt cayleyAngle (2 / (1 + x ^ 2)) x ∧
      cayleyHaarPullbackDensity x = cauchyDensity x := by
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ext <;> simp [unitCirclePhaseEmbedding, unitCircleCayleyMap, Real.cos_add_pi,
      Real.sin_add_pi]
  · simpa [cayleyAngle, two_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_arctan x).const_mul 2
  · simp [cayleyHaarPullbackDensity, cauchyDensity, div_eq_mul_inv, mul_left_comm, mul_comm]

end

end Omega.UnitCirclePhaseArithmetic
