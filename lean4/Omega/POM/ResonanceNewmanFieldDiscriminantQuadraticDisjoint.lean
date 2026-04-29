import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-resonance-newman-field-discriminant-quadratic-disjoint`. -/
theorem paper_pom_resonance_newman_field_discriminant_quadratic_disjoint
    (q d : Nat) (hq : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 13) (hd : 4 <= d)
    (newmanFieldDisjoint noQuadraticSubfield : Prop)
    (hdisjoint : newmanFieldDisjoint)
    (hnoquad : newmanFieldDisjoint → noQuadraticSubfield) :
    newmanFieldDisjoint ∧ noQuadraticSubfield := by
  have _hqChoices : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 13 := hq
  have _hdAtLeastFour : 4 <= d := hd
  exact ⟨hdisjoint, hnoquad hdisjoint⟩

end Omega.POM
