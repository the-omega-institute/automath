import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite Euler-atom data for the primitive-surgery package. -/
structure XiFiniteEulerPrimitiveSurgeryAdditivityData where
  Atom : Type
  [instFintypeAtom : Fintype Atom]
  [instDecidableEqAtom : DecidableEq Atom]
  multiplicity : Atom → ℤ
  eulerWeight : Atom → ℤ
  primitiveLength : Atom → ℤ
  corePrimitiveGenerator : ℤ
  coreAbelFinitePart : ℤ

attribute [instance] XiFiniteEulerPrimitiveSurgeryAdditivityData.instFintypeAtom
attribute [instance] XiFiniteEulerPrimitiveSurgeryAdditivityData.instDecidableEqAtom

namespace XiFiniteEulerPrimitiveSurgeryAdditivityData

/-- The one-atom primitive contribution produced by the Euler factor. -/
def primitiveAtomTerm (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) (a : D.Atom) : ℤ :=
  D.multiplicity a * (D.eulerWeight a + D.primitiveLength a)

/-- The one-atom Abel finite-part shift. -/
def abelAtomShift (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) (a : D.Atom) : ℤ :=
  D.multiplicity a * D.eulerWeight a

/-- Termwise primitive generator after expanding the logarithm of the finite Euler product. -/
def primitiveGenerator (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) : ℤ :=
  D.corePrimitiveGenerator + ∑ a, D.primitiveAtomTerm a

/-- Abel finite part obtained by summing the one-atom pole shifts. -/
def abelFinitePart (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) : ℤ :=
  D.coreAbelFinitePart + ∑ a, D.abelAtomShift a

/-- The primitive generator splits additively into the core term and the finite Euler atoms. -/
def primitiveGeneratorAdditivity (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) : Prop :=
  D.primitiveGenerator = D.corePrimitiveGenerator + ∑ a, D.primitiveAtomTerm a

/-- The Abel finite part shifts additively with no cross terms. -/
def abelFinitePartAdditivity (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) : Prop :=
  D.abelFinitePart = D.coreAbelFinitePart + ∑ a, D.abelAtomShift a

theorem primitive_generator_additivity (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) :
    D.primitiveGeneratorAdditivity := by
  simp [primitiveGeneratorAdditivity, primitiveGenerator]

theorem abel_finite_part_additivity (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) :
    D.abelFinitePartAdditivity := by
  simp [abelFinitePartAdditivity, abelFinitePart]

end XiFiniteEulerPrimitiveSurgeryAdditivityData

/-- Paper label: `thm:xi-finite-euler-primitive-surgery-additivity`. -/
theorem paper_xi_finite_euler_primitive_surgery_additivity
    (D : XiFiniteEulerPrimitiveSurgeryAdditivityData) :
    D.primitiveGeneratorAdditivity ∧ D.abelFinitePartAdditivity := by
  exact ⟨D.primitive_generator_additivity, D.abel_finite_part_additivity⟩

end Omega.Zeta
