import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The normalized Cauchy-minor mass attached to a finite family of minors. -/
noncomputable def conclusion_anchor_mobius_cauchy_minor_probability_invariance_mass
    {α : Type} [DecidableEq α] (Ω : Finset α) (minorMass : α → ℝ) (i : α) : ℝ :=
  minorMass i / Finset.sum Ω minorMass

/-- Paper-facing package for the finite Cauchy--Binet probability law: normalized minor weights
sum to one, and a common Möbius covariance factor cancels from numerator and denominator. -/
def conclusion_anchor_mobius_cauchy_minor_probability_invariance_statement : Prop :=
  ∀ {α : Type} [DecidableEq α] (Ω : Finset α) (minorMass : α → ℝ) (scale : ℝ),
    Finset.sum Ω minorMass ≠ 0 →
      scale ≠ 0 →
      (Finset.sum Ω (fun i =>
          conclusion_anchor_mobius_cauchy_minor_probability_invariance_mass Ω minorMass i) =
          1) ∧
        ∀ i ∈ Ω,
          conclusion_anchor_mobius_cauchy_minor_probability_invariance_mass Ω
              (fun j => scale * minorMass j) i =
            conclusion_anchor_mobius_cauchy_minor_probability_invariance_mass Ω minorMass i

/-- Paper label:
`thm:conclusion-anchor-mobius-cauchy-minor-probability-invariance`. -/
theorem paper_conclusion_anchor_mobius_cauchy_minor_probability_invariance :
    conclusion_anchor_mobius_cauchy_minor_probability_invariance_statement := by
  intro α _ Ω minorMass scale hsum hscale
  constructor
  · change Finset.sum Ω (fun i => minorMass i / Finset.sum Ω minorMass) = 1
    rw [← Finset.sum_div]
    exact div_self hsum
  · intro i hi
    change scale * minorMass i / Finset.sum Ω (fun j => scale * minorMass j) =
      minorMass i / Finset.sum Ω minorMass
    have hsum_scale :
        Finset.sum Ω (fun j => scale * minorMass j) = scale * Finset.sum Ω minorMass := by
      rw [← Finset.mul_sum]
    rw [hsum_scale]
    field_simp [hsum, hscale]

end Omega.Conclusion
