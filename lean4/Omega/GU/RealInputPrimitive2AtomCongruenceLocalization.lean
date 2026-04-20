import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.GU.RealInputLength2PrimitiveAtom

namespace Omega.GU

noncomputable section

/-- The explicit primitive length-two atom `u * z^2`. -/
def primitive2Atom (u z : ℂ) : ℂ :=
  u * z ^ 2

/-- The residue class singled out by the length-two atom modulo `q`. -/
def primitive2AtomResidueClass (q : ℕ) : ℕ :=
  2 % q

/-- The congruence-localized mass of the primitive length-two atom. -/
def primitive2AtomCongruenceMass (q a : ℕ) : ℂ :=
  if a % q = primitive2AtomResidueClass q then primitive2Atom 1 1 else 0

/-- Concrete congruence localization statement for the primitive length-two atom. -/
def Primitive2AtomCongruenceLocalizationStatement (q a : ℕ) : Prop :=
  primitive2AtomResidueClass q < q ∧
    (primitive2AtomCongruenceMass q a =
      if a % q = primitive2AtomResidueClass q then primitive2Atom 1 1 else 0) ∧
    (primitive2AtomCongruenceMass q a = primitive2Atom 1 1 ↔
      a % q = primitive2AtomResidueClass q)

/-- Paper label: `thm:gut-real-input-primitive-2-atom-congruence-localization`. The explicit
`u * z^2` atom survives the congruence filter exactly in the residue class `2 mod q`. -/
theorem paper_gut_real_input_primitive_2_atom_congruence_localization (q a : ℕ) (hq : 2 ≤ q) :
    Primitive2AtomCongruenceLocalizationStatement q a := by
  have hq0 : 0 < q := by omega
  refine ⟨?_, rfl, ?_⟩
  · simpa [primitive2AtomResidueClass] using Nat.mod_lt 2 hq0
  · by_cases h : a % q = primitive2AtomResidueClass q
    · simp [primitive2AtomCongruenceMass, primitive2Atom, h]
    · simp [primitive2AtomCongruenceMass, primitive2Atom, h]

end

end Omega.GU
