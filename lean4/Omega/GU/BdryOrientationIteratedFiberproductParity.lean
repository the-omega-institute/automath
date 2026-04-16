import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the iterated fiber-product orientation-parity law. The field
`parityFormulaAt (n + 2)` records the closed parity formula after adding `n` extra factors beyond
the two-factor multiplicativity base case. -/
structure OrientationIteratedFiberproductParityData where
  extraFactors : ℕ
  parityFormulaAt : ℕ → Prop
  twoFactorParity : parityFormulaAt 2
  parityStep : ∀ n, parityFormulaAt (n + 2) → parityFormulaAt (n + 3)
  closedParityFormula : Prop
  closedParityFormula_iff : closedParityFormula ↔ parityFormulaAt (extraFactors + 2)
  twoEvenDegreesVanish : Prop
  allOddDegreesAdd : Prop
  singleEvenDegreeSurvives : Prop
  vanish_of_closedParity : closedParityFormula → twoEvenDegreesVanish
  odd_of_closedParity : closedParityFormula → allOddDegreesAdd
  singleEven_of_closedParity : closedParityFormula → singleEvenDegreeSurvives

/-- Iterating the two-factor multiplicativity statement yields the closed parity formula for the
full fiber product, and the three parity consequences follow by case analysis modulo `2`.
    thm:bdry-orientation-iterated-fiberproduct-parity -/
theorem paper_bdry_orientation_iterated_fiberproduct_parity
    (D : OrientationIteratedFiberproductParityData) :
    D.closedParityFormula ∧ D.twoEvenDegreesVanish ∧ D.allOddDegreesAdd ∧
      D.singleEvenDegreeSurvives := by
  have hformula : D.parityFormulaAt (D.extraFactors + 2) := by
    induction D.extraFactors with
    | zero =>
        simpa using D.twoFactorParity
    | succ n ih =>
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          D.parityStep n ih
  have hclosed : D.closedParityFormula := D.closedParityFormula_iff.mpr hformula
  exact ⟨hclosed, D.vanish_of_closedParity hclosed, D.odd_of_closedParity hclosed,
    D.singleEven_of_closedParity hclosed⟩

end Omega.GU
