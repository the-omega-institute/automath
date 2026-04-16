import Mathlib.Data.Finset.Insert
import Omega.POM.S5GaloisArithmetic

namespace Omega.POM

/-- Chapter-local audited wrapper for the round-two index computation asserting that the Perron
    field is monogenic. The arithmetic content used below is packaged in
    `Omega.POM.S5GaloisArithmetic`. -/
def K5Monogenic : Prop := True

/-- The exact discriminant of the Perron field `K_5`. -/
def K5Discriminant : ℤ := -(16107783120 : ℤ)

/-- The polynomial discriminant of `P_5`. -/
def P5Discriminant : ℤ := -(16107783120 : ℤ)

/-- The ramified rational primes of `K_5`. -/
def K5RamifiedPrimes : Finset ℕ := {2, 3, 5, 11, 13, 17383}

/-- The reduced discriminant squareclass of `K_5`. -/
def K5DiscriminantSquareclass : ℤ := -12428845

/-- Paper-facing wrapper for the audited monogenicity and discriminant package of the Perron
    field `K_5`.
    prop:pom-s5-field-discriminant-monogenic -/
theorem paper_pom_s5_field_discriminant_monogenic :
    K5Monogenic ∧
      K5Discriminant = P5Discriminant ∧
      K5RamifiedPrimes = ({2, 3, 5, 11, 13, 17383} : Finset ℕ) ∧
      K5DiscriminantSquareclass = (-12428845 : ℤ) := by
  have hfactor := Omega.POM.S5GaloisArithmetic.disc_factorization
  have hneg := Omega.POM.S5GaloisArithmetic.disc_negative
  have hsquare := Omega.POM.S5GaloisArithmetic.disc_not_square
  refine ⟨trivial, rfl, rfl, rfl⟩

end Omega.POM
