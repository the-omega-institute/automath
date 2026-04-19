import Omega.POM.HankelDeterminantGeometricLaw

namespace Omega.POM

/-- Concrete integer-valued data for the bad-prime support bound coming from a geometric Hankel
determinant law. The determinant at lag `r` is `det₀ * ratio^r`, so the first two adjacent
determinants are `det₀` and `det₀ * ratio`. -/
structure POMHankelBadPrimesTwoDeterminantsData where
  det₀ : ℕ
  ratio : ℕ

namespace POMHankelBadPrimesTwoDeterminantsData

/-- The shifted Hankel determinant sequence. -/
def determinantSequence (D : POMHankelBadPrimesTwoDeterminantsData) (r : ℕ) : ℕ :=
  D.det₀ * D.ratio ^ r

/-- The first determinant in the audited adjacent pair. -/
def firstDeterminant (D : POMHankelBadPrimesTwoDeterminantsData) : ℕ :=
  D.determinantSequence 0

/-- The second determinant in the audited adjacent pair. -/
def secondDeterminant (D : POMHankelBadPrimesTwoDeterminantsData) : ℕ :=
  D.determinantSequence 1

/-- Every prime dividing any later determinant already divides the product of the first two
adjacent determinants. -/
def badPrimeSupportBound (D : POMHankelBadPrimesTwoDeterminantsData) : Prop :=
  ∀ p r, Nat.Prime p → p ∣ D.determinantSequence r →
    p ∣ D.firstDeterminant * D.secondDeterminant

lemma determinant_sequence_geometric (D : POMHankelBadPrimesTwoDeterminantsData) :
    ∀ r, D.determinantSequence r = D.det₀ * D.ratio ^ r := by
  intro r
  rfl

lemma secondDeterminant_eq (D : POMHankelBadPrimesTwoDeterminantsData) :
    D.secondDeterminant = D.det₀ * D.ratio := by
  simp [secondDeterminant, determinantSequence]

end POMHankelBadPrimesTwoDeterminantsData

open POMHankelBadPrimesTwoDeterminantsData

/-- Once the shifted Hankel determinant law is geometric, every prime dividing any later
determinant already divides the product of the first two adjacent determinants.
    prop:pom-hankel-bad-primes-two-determinants -/
theorem paper_pom_hankel_bad_primes_two_determinants (D : POMHankelBadPrimesTwoDeterminantsData) :
    D.badPrimeSupportBound := by
  intro p r hp hdiv
  cases r with
  | zero =>
      simpa [POMHankelBadPrimesTwoDeterminantsData.firstDeterminant,
        POMHankelBadPrimesTwoDeterminantsData.secondDeterminant,
        POMHankelBadPrimesTwoDeterminantsData.determinantSequence] using
        dvd_mul_of_dvd_left hdiv D.secondDeterminant
  | succ r =>
      rw [D.determinant_sequence_geometric (Nat.succ r)] at hdiv
      rcases hp.dvd_or_dvd hdiv with hbase | hpow
      · simpa [POMHankelBadPrimesTwoDeterminantsData.firstDeterminant,
          POMHankelBadPrimesTwoDeterminantsData.secondDeterminant,
          POMHankelBadPrimesTwoDeterminantsData.determinantSequence] using
          dvd_mul_of_dvd_left hbase D.secondDeterminant
      · have hratio : p ∣ D.ratio := hp.dvd_of_dvd_pow hpow
        have hsecond : p ∣ D.secondDeterminant := by
          rw [D.secondDeterminant_eq]
          exact dvd_mul_of_dvd_right hratio D.det₀
        exact dvd_mul_of_dvd_right hsecond D.firstDeterminant

end Omega.POM
