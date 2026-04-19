import Mathlib.Tactic
import Omega.Conclusion.QuadraticFieldRamification
import Omega.POM.S5GaloisArithmetic

namespace Omega.Conclusion

/-- The order of the unique index-two quotient extracted from the `S₅` package. -/
def ellipticT5IndexTwoQuotientOrder : ℕ := Nat.factorial 5 / 2

/-- The quadratic discriminant singled out by the `T₅` package. -/
def ellipticT5QuadraticSubfieldDiscriminant : ℤ := 5

/-- Concrete formulation of the unique quadratic subfield claim for the `T₅` package. -/
def ellipticT5UniqueQuadraticSubfield : Prop :=
  Nat.factorial 5 = 2 * ellipticT5IndexTwoQuotientOrder ∧
    Omega.Conclusion.QuadraticFieldRamification.quadDisc
        ellipticT5QuadraticSubfieldDiscriminant = 5 ∧
      ∀ d : ℤ,
        Omega.Conclusion.QuadraticFieldRamification.quadDisc d = 5 →
          d = ellipticT5QuadraticSubfieldDiscriminant

lemma quadDisc_eq_five_unique (d : ℤ)
    (h : Omega.Conclusion.QuadraticFieldRamification.quadDisc d = 5) : d = 5 := by
  by_cases hd : d % 4 = 1
  · simpa [Omega.Conclusion.QuadraticFieldRamification.quadDisc, hd] using h
  · have h' : 4 * d = 5 := by
      simpa [Omega.Conclusion.QuadraticFieldRamification.quadDisc, hd] using h
    have hmod := congrArg (fun z : ℤ => z % 4) h'
    norm_num at hmod

/-- The `T₅` Galois package has a single index-two quotient and the discriminant squareclass is
`5`, so the quadratic subfield is `Q(√5)`.
    thm:conclusion-elliptic-t5-unique-quadratic-subfield -/
theorem paper_conclusion_elliptic_t5_unique_quadratic_subfield :
    ellipticT5UniqueQuadraticSubfield := by
  refine ⟨?_, ?_, ?_⟩
  · have hs5 : Nat.factorial 5 = 120 := Omega.POM.S5GaloisArithmetic.s5_order
    have ha5 : Nat.factorial 5 / 2 = 60 := Omega.POM.S5GaloisArithmetic.a5_order
    unfold ellipticT5IndexTwoQuotientOrder
    omega
  · simpa [ellipticT5QuadraticSubfieldDiscriminant] using
      Omega.Conclusion.QuadraticFieldRamification.disc_sqrt5
  · intro d hd
    simpa [ellipticT5QuadraticSubfieldDiscriminant] using quadDisc_eq_five_unique d hd

end Omega.Conclusion
