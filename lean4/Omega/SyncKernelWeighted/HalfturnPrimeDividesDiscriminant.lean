import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped Polynomial

noncomputable section

/-- Concrete half-turn package: the even polynomial `widehat_p_n(s)` is obtained from the
auxiliary polynomial `f_n(u)` by the square substitution `u = s^2`, and the constant term carries
the divisibility information at the half-turn point `s = 0`. -/
structure halfturn_prime_divides_discriminant_data where
  p : ℤ
  constantTerm : ℤ
  constant_dvd : p ∣ constantTerm

/-- The auxiliary polynomial `f_n(u) = u + c`. -/
def halfturn_prime_divides_discriminant_fn
    (D : halfturn_prime_divides_discriminant_data) : Polynomial ℤ :=
  Polynomial.C D.constantTerm + Polynomial.X

/-- The even polynomial `widehat_p_n(s) = f_n(s^2) = s^2 + c`. -/
def halfturn_prime_divides_discriminant_widehat
    (D : halfturn_prime_divides_discriminant_data) : Polynomial ℤ :=
  Polynomial.C D.constantTerm + Polynomial.X ^ 2

/-- The repeated-root witness at the half-turn point `s = 0`: both the polynomial and its
derivative vanish modulo every divisor of the constant term. -/
def halfturn_prime_divides_discriminant_repeated_root_witness
    (D : halfturn_prime_divides_discriminant_data) : Prop :=
  D.p ∣ (halfturn_prime_divides_discriminant_widehat D).eval 0 ∧
    D.p ∣ (Polynomial.derivative (halfturn_prime_divides_discriminant_widehat D)).eval 0

/-- Explicit quadratic discriminant of `s^2 + c`. -/
def halfturn_prime_divides_discriminant_discriminant
    (D : halfturn_prime_divides_discriminant_data) : ℤ :=
  -4 * D.constantTerm

/-- Paper-facing toy model of the half-turn discriminant divisibility argument. The square
substitution makes the reduced polynomial acquire a repeated root at `s = 0`, and the resulting
quadratic discriminant is visibly divisible by every prime dividing the half-turn constant term. -/
def halfturn_prime_divides_discriminant_data.statement
    (D : halfturn_prime_divides_discriminant_data) : Prop :=
  halfturn_prime_divides_discriminant_widehat D =
      (halfturn_prime_divides_discriminant_fn D).comp (Polynomial.X ^ 2) ∧
    D.p ∣ (halfturn_prime_divides_discriminant_fn D).eval 0 ∧
    halfturn_prime_divides_discriminant_repeated_root_witness D ∧
    D.p ∣ halfturn_prime_divides_discriminant_discriminant D

/-- Paper label: `prop:halfturn-prime-divides-discriminant`. -/
theorem paper_halfturn_prime_divides_discriminant
    (D : halfturn_prime_divides_discriminant_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold halfturn_prime_divides_discriminant_widehat halfturn_prime_divides_discriminant_fn
    rw [Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
  · simpa [halfturn_prime_divides_discriminant_fn] using D.constant_dvd
  · refine ⟨?_, ?_⟩
    · simpa [halfturn_prime_divides_discriminant_repeated_root_witness,
        halfturn_prime_divides_discriminant_widehat, halfturn_prime_divides_discriminant_fn] using
        D.constant_dvd
    · simp [halfturn_prime_divides_discriminant_repeated_root_witness,
        halfturn_prime_divides_discriminant_widehat]
  · rcases D.constant_dvd with ⟨k, hk⟩
    refine ⟨-4 * k, ?_⟩
    simp [halfturn_prime_divides_discriminant_discriminant, hk, mul_assoc, mul_left_comm,
      mul_comm]

end

end Omega.SyncKernelWeighted
