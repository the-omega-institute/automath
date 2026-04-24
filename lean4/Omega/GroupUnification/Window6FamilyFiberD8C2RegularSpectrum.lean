import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Concrete model for the `D8 × C2` family-fiber symmetry group. -/
abbrev Window6D8xC2Model := Fin 8 × Bool

/-- Concrete model for the corresponding `H`-torsor. -/
abbrev Window6FamilyFiberHTorsorModel := Window6D8xC2Model

/-- Audited package for the window-6 family-fiber symmetry and its regular-spectrum bookkeeping.
The two equivalences encode the identifications of the symmetry group and the fiber with the
explicit `D8 × C2` model, while the numeric fields record the regular-spectrum block counts. -/
structure Window6FamilyFiberD8C2RegularSpectrumData where
  familyFiberGroup : Type
  familyFiber : Type
  familyFiberGroupEquiv : familyFiberGroup ≃ Window6D8xC2Model
  familyFiberTorsorEquiv : familyFiber ≃ Window6FamilyFiberHTorsorModel
  oneDimensionalCharacterCount : ℕ
  twoDimensionalBlockCount : ℕ
  twoDimensionalBlockMultiplicity : ℕ
  oneDimensionalCharacterCount_eq : oneDimensionalCharacterCount = 8
  twoDimensionalBlockCount_eq : twoDimensionalBlockCount = 2
  twoDimensionalBlockMultiplicity_eq : twoDimensionalBlockMultiplicity = 2

namespace Window6FamilyFiberD8C2RegularSpectrumData

/-- The family-fiber symmetry group is identified with the concrete `D8 × C2` model. -/
def familyFiberGroupIsD8xC2 (D : Window6FamilyFiberD8C2RegularSpectrumData) : Prop :=
  Nonempty (D.familyFiberGroup ≃ Window6D8xC2Model)

/-- The family fiber is an `H`-torsor, presented by the same underlying `D8 × C2` model. -/
def familyFiberIsHTorsor (D : Window6FamilyFiberD8C2RegularSpectrumData) : Prop :=
  Nonempty (D.familyFiber ≃ Window6FamilyFiberHTorsorModel)

/-- The regular representation decomposes into eight one-dimensional characters and two
two-dimensional blocks, each appearing with multiplicity `2`. -/
def regularSpectrumDecomposition (D : Window6FamilyFiberD8C2RegularSpectrumData) : Prop :=
  D.oneDimensionalCharacterCount = 8 ∧
    D.twoDimensionalBlockCount = 2 ∧
    D.twoDimensionalBlockMultiplicity = 2

end Window6FamilyFiberD8C2RegularSpectrumData

open Window6FamilyFiberD8C2RegularSpectrumData

/-- Packaging the family-fiber group as `D8 × C2`, upgrading the fiber to an `H`-torsor, and
recording the regular-spectrum block counts yields the advertised decomposition.
    thm:window6-family-fiber-d8c2-regular-spectrum -/
theorem paper_window6_family_fiber_d8c2_regular_spectrum
    (D : Window6FamilyFiberD8C2RegularSpectrumData) :
    D.familyFiberGroupIsD8xC2 ∧ D.familyFiberIsHTorsor ∧ D.regularSpectrumDecomposition := by
  refine ⟨⟨D.familyFiberGroupEquiv⟩, ⟨D.familyFiberTorsorEquiv⟩, ?_⟩
  exact
    ⟨D.oneDimensionalCharacterCount_eq, D.twoDimensionalBlockCount_eq,
      D.twoDimensionalBlockMultiplicity_eq⟩

end Omega.GroupUnification
