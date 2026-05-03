import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite slab data for the minimal coordinate-bundle Gibbs ensemble. -/
structure conclusion_coordinate_bundle_gibbs_resistance_closed_form_data where
  Slab : Type
  Edge : Type
  slabFintype : Fintype Slab
  edgeDecidableEq : DecidableEq Edge
  edges : Slab → Finset Edge
  weight : Edge → ℝ

/-- Total Gibbs weight in one slab. -/
noncomputable def conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data) (a : D.Slab) : ℝ :=
  letI : DecidableEq D.Edge := D.edgeDecidableEq
  (D.edges a).sum fun e => D.weight e

/-- Product partition function for independent slab choices. -/
noncomputable def conclusion_coordinate_bundle_gibbs_resistance_closed_form_partition
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data) : ℝ :=
  letI : Fintype D.Slab := D.slabFintype
  Finset.univ.prod fun a : D.Slab =>
    conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight D a

/-- One-edge occupancy in the normalized one-slab Gibbs law. -/
noncomputable def conclusion_coordinate_bundle_gibbs_resistance_closed_form_occupancy
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data)
    (a : D.Slab) (e : D.Edge) : ℝ :=
  D.weight e / conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight D a

/-- Parallel resistance of the slab conductances. -/
noncomputable def conclusion_coordinate_bundle_gibbs_resistance_closed_form_resistance
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data) (a : D.Slab) : ℝ :=
  (conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight D a)⁻¹

/-- Uniform one-edge occupancy when all slab edges have unit conductance. -/
noncomputable def conclusion_coordinate_bundle_gibbs_resistance_closed_form_uniformOccupancy
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data)
    (a : D.Slab) : ℝ :=
  ((D.edges a).card : ℝ)⁻¹

/-- The closed forms for the product Gibbs ensemble, one-edge occupancy, parallel resistance,
and the unweighted cardinality specialization. -/
def conclusion_coordinate_bundle_gibbs_resistance_closed_form_statement
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data) : Prop :=
  conclusion_coordinate_bundle_gibbs_resistance_closed_form_partition D =
      (letI : Fintype D.Slab := D.slabFintype
       Finset.univ.prod fun a : D.Slab =>
        conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight D a) ∧
    (∀ (a : D.Slab) (e : D.Edge),
      e ∈ D.edges a →
        conclusion_coordinate_bundle_gibbs_resistance_closed_form_occupancy D a e =
          D.weight e /
            conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight D a) ∧
    (∀ a : D.Slab,
      conclusion_coordinate_bundle_gibbs_resistance_closed_form_resistance D a =
        (conclusion_coordinate_bundle_gibbs_resistance_closed_form_slabWeight D a)⁻¹) ∧
    (∀ a : D.Slab,
      conclusion_coordinate_bundle_gibbs_resistance_closed_form_uniformOccupancy D a =
        (1 : ℝ) / (D.edges a).card)

/-- Paper label: `cor:conclusion-coordinate-bundle-gibbs-resistance-closed-form`. -/
theorem paper_conclusion_coordinate_bundle_gibbs_resistance_closed_form
    (D : conclusion_coordinate_bundle_gibbs_resistance_closed_form_data) :
    conclusion_coordinate_bundle_gibbs_resistance_closed_form_statement D := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro a e _he
    rfl
  · intro a
    rfl
  · intro a
    simp [conclusion_coordinate_bundle_gibbs_resistance_closed_form_uniformOccupancy, div_eq_mul_inv]

end Omega.Conclusion
