import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finiteness of the Legendre--Fenchel transform at slope `α`, expressed as boundedness above
of the concrete affine-pressure family. -/
def conclusion_realinput40_output_density_halfsaturation_support_legendre_finite
    (P : ℝ → ℝ) (α : ℝ) : Prop :=
  ∃ C : ℝ, ∀ θ : ℝ, θ * α - P θ ≤ C

/-- The left pressure tail makes every negative slope have infinite Legendre cost. -/
def conclusion_realinput40_output_density_halfsaturation_support_left_tail
    (P : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, α < 0 →
    ¬ conclusion_realinput40_output_density_halfsaturation_support_legendre_finite P α

/-- The right pressure tail makes every slope above `1/2` have infinite Legendre cost. -/
def conclusion_realinput40_output_density_halfsaturation_support_right_tail
    (P : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, (1 / 2 : ℝ) < α →
    ¬ conclusion_realinput40_output_density_halfsaturation_support_legendre_finite P α

/-- The convex pressure interpolation supplies finite Legendre cost throughout the closed slope
interval determined by the two endpoint tails. -/
def conclusion_realinput40_output_density_halfsaturation_support_convex
    (P : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ (1 / 2 : ℝ) →
    conclusion_realinput40_output_density_halfsaturation_support_legendre_finite P α

/-- Paper label: `thm:conclusion-realinput40-output-density-halfsaturation-support`. -/
theorem paper_conclusion_realinput40_output_density_halfsaturation_support
    (P : ℝ → ℝ)
    (hleft : conclusion_realinput40_output_density_halfsaturation_support_left_tail P)
    (hright : conclusion_realinput40_output_density_halfsaturation_support_right_tail P)
    (hconvex : conclusion_realinput40_output_density_halfsaturation_support_convex P) :
    ∀ α : ℝ,
      conclusion_realinput40_output_density_halfsaturation_support_legendre_finite P α ↔
        0 ≤ α ∧ α ≤ (1 / 2 : ℝ) := by
  intro α
  constructor
  · intro hfinite
    constructor
    · by_contra hnonneg
      exact (hleft α (lt_of_not_ge hnonneg)) hfinite
    · by_contra hhalf
      exact (hright α (lt_of_not_ge hhalf)) hfinite
  · intro hinterval
    exact hconvex α hinterval.1 hinterval.2

end Omega.Conclusion
