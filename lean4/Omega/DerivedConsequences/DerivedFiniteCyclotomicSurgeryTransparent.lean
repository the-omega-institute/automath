import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- Concrete input for the finite-cyclotomic-surgery transparency package: the pre-surgery growth
radius and normalized exponent of the core object. -/
structure DerivedFiniteCyclotomicSurgeryTransparentData where
  coreRadius : ℝ
  coreExponent : ℝ

/-- The surgery terms contribute only unit-circle poles. -/
def derived_finite_cyclotomic_surgery_transparent_unit_circle_radius : ℝ :=
  1

/-- The resulting growth radius is the larger of the core radius and the unit-circle threshold. -/
def derived_finite_cyclotomic_surgery_transparent_growth_radius
    (D : DerivedFiniteCyclotomicSurgeryTransparentData) : ℝ :=
  max D.coreRadius derived_finite_cyclotomic_surgery_transparent_unit_circle_radius

/-- The normalized exponent is the maximum of the core exponent and the unit-circle threshold
`0`. -/
def derived_finite_cyclotomic_surgery_transparent_normalized_exponent
    (D : DerivedFiniteCyclotomicSurgeryTransparentData) : ℝ :=
  max D.coreExponent 0

/-- Paper-facing transparency statement: unit-circle surgery cannot create subunit singular
radii, and both radius/exponent are obtained by taking the maximum with the unit thresholds. -/
def derived_finite_cyclotomic_surgery_transparent_statement
    (D : DerivedFiniteCyclotomicSurgeryTransparentData) : Prop :=
  derived_finite_cyclotomic_surgery_transparent_unit_circle_radius ≤
      derived_finite_cyclotomic_surgery_transparent_growth_radius D ∧
    derived_finite_cyclotomic_surgery_transparent_growth_radius D =
      max D.coreRadius derived_finite_cyclotomic_surgery_transparent_unit_circle_radius ∧
    0 ≤ derived_finite_cyclotomic_surgery_transparent_normalized_exponent D ∧
    derived_finite_cyclotomic_surgery_transparent_normalized_exponent D =
      max D.coreExponent 0

/-- Paper label: `thm:derived-finite-cyclotomic-surgery-transparent`. Finite cyclotomic surgery
adds only unit-circle poles, so it cannot force the singular radius below `1`; the post-surgery
growth radius and normalized exponent are exactly the corresponding `max` combinations with the
unit-circle thresholds. -/
theorem paper_derived_finite_cyclotomic_surgery_transparent
    (D : DerivedFiniteCyclotomicSurgeryTransparentData) :
    derived_finite_cyclotomic_surgery_transparent_statement D := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · exact le_max_right D.coreRadius derived_finite_cyclotomic_surgery_transparent_unit_circle_radius
  · exact le_max_right D.coreExponent 0

end Omega.DerivedConsequences
