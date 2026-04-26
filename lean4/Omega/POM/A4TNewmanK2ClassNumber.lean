import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete audited scalar data for the Newman critical quadratic subfield package. -/
structure pom_a4t_newman_k2_class_number_data where
  squarefreeDiscriminantPart : ℤ
  classNumber : ℕ
  squarefreeDiscriminantPart_h : squarefreeDiscriminantPart = -1151
  classNumber_h : classNumber = 41

namespace pom_a4t_newman_k2_class_number_data

/-- The paper's quadratic subfield fingerprint. -/
def quadraticSubfieldDiscriminantPart (D : pom_a4t_newman_k2_class_number_data) : ℤ :=
  D.squarefreeDiscriminantPart

/-- Concrete cyclic model for the class group when the audited class number is fixed. -/
abbrev classGroupModel (D : pom_a4t_newman_k2_class_number_data) := ZMod D.classNumber

/-- The Hilbert class field degree is the class number. -/
def hilbertClassFieldDegree (D : pom_a4t_newman_k2_class_number_data) : ℕ :=
  D.classNumber

/-- Concrete cyclic model for `Gal(H / K₂)`. -/
abbrev hilbertClassFieldGaloisGroup (D : pom_a4t_newman_k2_class_number_data) := ZMod D.classNumber

/-- Concrete dihedral model for the Galois closure over `ℚ`. -/
abbrev galoisClosureGroup (D : pom_a4t_newman_k2_class_number_data) :=
  DihedralGroup D.classNumber

/-- The quadratic base extension doubles the Hilbert class field degree. -/
def galoisClosureDegreeOverQ (D : pom_a4t_newman_k2_class_number_data) : ℕ :=
  2 * D.classNumber

/-- Paper-facing conjunction of the quadratic-subfield fingerprint, the prime class number, the
cyclic class-group and Hilbert-class-field Galois models, and the order-`82` dihedral closure
model. -/
def statement (D : pom_a4t_newman_k2_class_number_data) : Prop :=
  D.quadraticSubfieldDiscriminantPart = -1151 ∧
    D.classNumber = 41 ∧
    IsAddCyclic D.classGroupModel ∧
    Nat.card D.classGroupModel = 41 ∧
    D.hilbertClassFieldDegree = 41 ∧
    IsAddCyclic D.hilbertClassFieldGaloisGroup ∧
    Nat.card D.hilbertClassFieldGaloisGroup = 41 ∧
    D.galoisClosureDegreeOverQ = 82 ∧
    Nat.card D.galoisClosureGroup = 82

end pom_a4t_newman_k2_class_number_data

open pom_a4t_newman_k2_class_number_data

/-- Paper label: `prop:pom-a4t-newman-k2-class-number`. The squarefree discriminant part is
`-1151`, the audited class number is `41`, the corresponding class-group and Hilbert-class-field
Galois models are cyclic of order `41`, and the closure over `ℚ` is modeled by the dihedral group
of order `82`. -/
theorem paper_pom_a4t_newman_k2_class_number
    (D : pom_a4t_newman_k2_class_number_data) : D.statement := by
  have hdisc : D.quadraticSubfieldDiscriminantPart = -1151 := by
    simpa [quadraticSubfieldDiscriminantPart] using D.squarefreeDiscriminantPart_h
  have hclass : D.classNumber = 41 := by
    exact D.classNumber_h
  haveI : Fact (Nat.Prime 41) := ⟨by decide⟩
  have hClassGroupCard : Nat.card D.classGroupModel = 41 := by
    rw [classGroupModel, hclass]
    simpa using (Nat.card_zmod 41)
  have hHilbertCard : Nat.card D.hilbertClassFieldGaloisGroup = 41 := by
    rw [hilbertClassFieldGaloisGroup, hclass]
    simpa using (Nat.card_zmod 41)
  have hClassGroupCyclic : IsAddCyclic D.classGroupModel := by
    exact isAddCyclic_of_prime_card hClassGroupCard
  have hHilbertCyclic : IsAddCyclic D.hilbertClassFieldGaloisGroup := by
    exact isAddCyclic_of_prime_card hHilbertCard
  have hClosureDegree : D.galoisClosureDegreeOverQ = 82 := by
    simpa [galoisClosureDegreeOverQ, hclass]
  have hClosureCard : Nat.card D.galoisClosureGroup = 82 := by
    rw [galoisClosureGroup, hclass]
    simpa using (DihedralGroup.nat_card (n := 41))
  exact ⟨hdisc, hclass, hClassGroupCyclic, hClassGroupCard,
    by simp [hilbertClassFieldDegree, hclass], hHilbertCyclic, hHilbertCard,
    hClosureDegree, hClosureCard⟩

end Omega.POM
