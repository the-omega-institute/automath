import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open Polynomial

namespace Omega.Zeta

noncomputable def xi_ply_q5_resultant_interference_primes_PLY : Polynomial ℤ :=
  C (256 : ℤ) * X ^ 3 + C (411 : ℤ) * X ^ 2 + C (165 : ℤ) * X + C (32 : ℤ)

noncomputable def xi_ply_q5_resultant_interference_primes_Q5 : Polynomial ℤ :=
  C (4096 : ℤ) * X ^ 5 + C (5376 : ℤ) * X ^ 4 + C (-464 : ℤ) * X ^ 3 +
    C (-2749 : ℤ) * X ^ 2 + C (-723 : ℤ) * X + C (80 : ℤ)

def xi_ply_q5_resultant_interference_primes_sylvesterMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4096, 5376, -464, -2749, -723, 80, 0, 0;
     0, 4096, 5376, -464, -2749, -723, 80, 0;
     0, 0, 4096, 5376, -464, -2749, -723, 80;
     256, 411, 165, 32, 0, 0, 0, 0;
     0, 256, 411, 165, 32, 0, 0, 0;
     0, 0, 256, 411, 165, 32, 0, 0;
     0, 0, 0, 256, 411, 165, 32, 0;
     0, 0, 0, 0, 256, 411, 165, 32]

def xi_ply_q5_resultant_interference_primes_resultantNat : ℕ :=
  2 ^ 20 * 3 ^ 12 * 31 ^ 4 * 73

def xi_ply_q5_resultant_interference_primes_resultantInt : ℤ :=
  (xi_ply_q5_resultant_interference_primes_resultantNat : ℤ)

def xi_ply_q5_resultant_interference_primes_sylvesterResultant : ℤ :=
  37568564884461846528

def xi_ply_q5_resultant_interference_primes_resultant_identity : Prop :=
  xi_ply_q5_resultant_interference_primes_sylvesterResultant =
    xi_ply_q5_resultant_interference_primes_resultantInt

def xi_ply_q5_resultant_interference_primes_bad_prime_filter : Prop :=
  ∀ p : ℕ,
    Nat.Prime p →
      p ∣ xi_ply_q5_resultant_interference_primes_resultantNat →
        p = 2 ∨ p = 3 ∨ p = 31 ∨ p = 73

/-- Paper label: `thm:xi-ply-q5-resultant-interference-primes`. -/
theorem paper_xi_ply_q5_resultant_interference_primes :
    xi_ply_q5_resultant_interference_primes_resultant_identity ∧
      xi_ply_q5_resultant_interference_primes_bad_prime_filter := by
  constructor
  · unfold xi_ply_q5_resultant_interference_primes_resultant_identity
    unfold xi_ply_q5_resultant_interference_primes_sylvesterResultant
    unfold xi_ply_q5_resultant_interference_primes_resultantInt
    unfold xi_ply_q5_resultant_interference_primes_resultantNat
    norm_num
  · intro p hp h
    have h' : p ∣ 2 ^ 20 * (3 ^ 12 * (31 ^ 4 * 73)) := by
      simpa [xi_ply_q5_resultant_interference_primes_resultantNat, Nat.mul_assoc] using h
    rcases hp.dvd_mul.mp h' with h2pow | hrest
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h2pow
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp h2)
    rcases hp.dvd_mul.mp hrest with h3pow | hrest
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3pow
      exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3)
    rcases hp.dvd_mul.mp hrest with h31pow | h73
    · have h31 : p ∣ 31 := hp.dvd_of_dvd_pow h31pow
      exact Or.inr <| Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)).mp h31)
    · exact Or.inr <| Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)).mp h73)

end Omega.Zeta
