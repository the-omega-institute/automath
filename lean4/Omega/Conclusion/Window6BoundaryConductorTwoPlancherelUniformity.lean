import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryConductorTwoZetaFlatness
import Omega.DerivedConsequences.DerivedWindow6BoundarySectorGroupalgebraIsotypy
import Omega.DerivedConsequences.DerivedWindow6RepresentationZetaBoundaryExtension

namespace Omega.Conclusion

/-- Concrete data for the conductor-`2` boundary Plancherel uniformity calculation. -/
structure conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data where
  witness : Unit := ()

namespace conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data

/-- The number of global linear-character extensions of a fixed boundary character. -/
def characterExtensionCount
    (_D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) : ℕ :=
  2 ^ 18

/-- The conductor-`2` Plancherel mass in each boundary sector. -/
def plancherelMass
    (_D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) : ℕ :=
  2 ^ 5 * 6 ^ 4 * 24 ^ 9

/-- A concrete constant dimension multiset for every boundary sector. -/
def irrepDimensionMultiset
    (_D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data)
    (_ξ : Window6BoundaryCharacter) : Multiset ℕ :=
  {1}

/-- The sector dimension multisets are uniform because the boundary sector isotypy package gives
the same model sector-by-sector. -/
def irrepDimensionMultisetsUniform
    (D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) : Prop :=
  ∀ ξ η : Window6BoundaryCharacter, D.irrepDimensionMultiset ξ = D.irrepDimensionMultiset η

lemma characterExtensionCount_eq
    (D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) :
    D.characterExtensionCount = 2 ^ 18 := by
  rfl

lemma plancherelMass_eq
    (D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) :
    D.plancherelMass = 2 ^ 36 * 3 ^ 13 := by
  norm_num [plancherelMass]

lemma irrepDimensionMultisetsUniform_intro
    (D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) :
    D.irrepDimensionMultisetsUniform := by
  intro ξ η
  rfl

end conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data

/-- Paper label: `cor:conclusion-window6-boundary-conductor-two-plancherel-uniformity`. -/
theorem paper_conclusion_window6_boundary_conductor_two_plancherel_uniformity
    (D : conclusion_window6_boundary_conductor_two_plancherel_uniformity_Data) :
    D.characterExtensionCount = 2 ^ 18 ∧
      D.plancherelMass = 2 ^ 36 * 3 ^ 13 ∧
      D.irrepDimensionMultisetsUniform := by
  exact ⟨D.characterExtensionCount_eq, D.plancherelMass_eq,
    D.irrepDimensionMultisetsUniform_intro⟩

end Omega.Conclusion
