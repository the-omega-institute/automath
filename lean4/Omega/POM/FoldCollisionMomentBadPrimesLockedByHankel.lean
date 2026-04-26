import Mathlib.Tactic
import Omega.POM.StiffZeroHankelGoodReductionDimStability

namespace Omega.POM

/-- The audited `k = 4` Hankel determinant `2^17 * 3^2`. -/
def pom_fold_collision_moment_bad_primes_locked_by_hankel_det4_nat : ℕ :=
  2 ^ 17 * 3 ^ 2

/-- The audited `k = 5` Hankel determinant `2^13 * 3^5 * 5^7`. -/
def pom_fold_collision_moment_bad_primes_locked_by_hankel_det5_nat : ℕ :=
  2 ^ 13 * 3 ^ 5 * 5 ^ 7

/-- The integer cast of the `k = 4` determinant. -/
def pom_fold_collision_moment_bad_primes_locked_by_hankel_det4 : ℤ :=
  pom_fold_collision_moment_bad_primes_locked_by_hankel_det4_nat

/-- The integer cast of the `k = 5` determinant. -/
def pom_fold_collision_moment_bad_primes_locked_by_hankel_det5 : ℤ :=
  pom_fold_collision_moment_bad_primes_locked_by_hankel_det5_nat

private theorem pom_fold_collision_moment_bad_primes_locked_by_hankel_prime_dvd_det4
    {p : ℕ} (hp : Nat.Prime p)
    (hpdvd : p ∣ pom_fold_collision_moment_bad_primes_locked_by_hankel_det4_nat) :
    p = 2 ∨ p = 3 := by
  have hmul : p ∣ 2 ^ 17 * 3 ^ 2 := by
    simpa [pom_fold_collision_moment_bad_primes_locked_by_hankel_det4_nat] using hpdvd
  rcases hp.dvd_mul.mp hmul with h2 | h3
  · left
    exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow h2)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow h3)

private theorem pom_fold_collision_moment_bad_primes_locked_by_hankel_prime_dvd_det5
    {p : ℕ} (hp : Nat.Prime p)
    (hpdvd : p ∣ pom_fold_collision_moment_bad_primes_locked_by_hankel_det5_nat) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  have hmul : p ∣ 2 ^ 13 * (3 ^ 5 * 5 ^ 7) := by
    simpa [pom_fold_collision_moment_bad_primes_locked_by_hankel_det5_nat, Nat.mul_assoc] using
      hpdvd
  rcases hp.dvd_mul.mp hmul with h2 | hrest
  · exact Or.inl <|
      (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow h2)
  · rcases hp.dvd_mul.mp hrest with h3 | h5
    · exact Or.inr <| Or.inl <|
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow h3)
    · exact Or.inr <| Or.inr <|
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp (hp.dvd_of_dvd_pow h5)

private theorem pom_fold_collision_moment_bad_primes_locked_by_hankel_not_dvd_det4
    {p : ℕ} (hp : Nat.Prime p) (hpge : 5 ≤ p) :
    ¬ ((p : ℤ) ∣ pom_fold_collision_moment_bad_primes_locked_by_hankel_det4) := by
  intro hdiv
  have hnat : p ∣ pom_fold_collision_moment_bad_primes_locked_by_hankel_det4_nat := by
    simpa [pom_fold_collision_moment_bad_primes_locked_by_hankel_det4,
      pom_fold_collision_moment_bad_primes_locked_by_hankel_det4_nat] using
      (Int.natCast_dvd_natCast.mp hdiv)
  rcases pom_fold_collision_moment_bad_primes_locked_by_hankel_prime_dvd_det4 hp hnat with
    h2 | h3
  · omega
  · omega

private theorem pom_fold_collision_moment_bad_primes_locked_by_hankel_not_dvd_det5
    {p : ℕ} (hp : Nat.Prime p) (hpge : 7 ≤ p) :
    ¬ ((p : ℤ) ∣ pom_fold_collision_moment_bad_primes_locked_by_hankel_det5) := by
  intro hdiv
  have hnat : p ∣ pom_fold_collision_moment_bad_primes_locked_by_hankel_det5_nat := by
    simpa [pom_fold_collision_moment_bad_primes_locked_by_hankel_det5,
      pom_fold_collision_moment_bad_primes_locked_by_hankel_det5_nat] using
      (Int.natCast_dvd_natCast.mp hdiv)
  rcases pom_fold_collision_moment_bad_primes_locked_by_hankel_prime_dvd_det5 hp hnat with
    h2 | h3 | h5
  · omega
  · omega
  · omega

/-- Paper label: `cor:pom-fold-collision-moment-bad-primes-locked-by-hankel`.
The audited determinant factorizations show that no prime `p ≥ 5` divides the `k = 4` witness and
no prime `p ≥ 7` divides the `k = 5` witness, so the good-reduction Hankel-rank stability theorem
applies verbatim in both cases. -/
theorem paper_pom_fold_collision_moment_bad_primes_locked_by_hankel
    {p : ℕ} [Fact p.Prime]
    (a4 a5 : ℕ → ℤ)
    (A4 A5 : Matrix (Fin 5) (Fin 5) ℤ)
    (hshift4 : hankelBlock 5 1 a4 = hankelBlock 5 0 a4 * A4)
    (hdet4 : (hankelBlock 5 0 a4).det =
      pom_fold_collision_moment_bad_primes_locked_by_hankel_det4)
    (hshift5 : hankelBlock 5 1 a5 = hankelBlock 5 0 a5 * A5)
    (hdet5 : (hankelBlock 5 0 a5).det =
      pom_fold_collision_moment_bad_primes_locked_by_hankel_det5) :
    (5 ≤ p →
      hankelTransitionDenominatorCleared a4 A4 ∧
        IsUnit ((hankelBlock 5 0 a4).map (Int.castRingHom (ZMod p))).det ∧
        Matrix.rank ((hankelBlock 5 0 a4).map (Int.castRingHom (ZMod p))) = 5) ∧
    (7 ≤ p →
      hankelTransitionDenominatorCleared a5 A5 ∧
        IsUnit ((hankelBlock 5 0 a5).map (Int.castRingHom (ZMod p))).det ∧
        Matrix.rank ((hankelBlock 5 0 a5).map (Int.castRingHom (ZMod p))) = 5) := by
  refine ⟨?_, ?_⟩
  · intro hpge
    have hp' : Nat.Prime p := Fact.out
    have hstiff4 : ¬ ((p : ℤ) ∣ (hankelBlock 5 0 a4).det) := by
      rw [hdet4]
      exact pom_fold_collision_moment_bad_primes_locked_by_hankel_not_dvd_det4 hp' hpge
    simpa using
      paper_pom_stiff0_hankel_good_reduction_dim_stability (d := 5) (p := p) a4 A4 hshift4 hstiff4
  · intro hpge
    have hp' : Nat.Prime p := Fact.out
    have hstiff5 : ¬ ((p : ℤ) ∣ (hankelBlock 5 0 a5).det) := by
      rw [hdet5]
      exact pom_fold_collision_moment_bad_primes_locked_by_hankel_not_dvd_det5 hp' hpge
    simpa using
      paper_pom_stiff0_hankel_good_reduction_dim_stability (d := 5) (p := p) a5 A5 hshift5 hstiff5

end Omega.POM
