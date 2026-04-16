import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial

namespace Omega

open Polynomial

/-- Pascal splitting for the path-independent-set coefficient recurrence. -/
private theorem choose_pathIndSet_recurrence (ℓ j : Nat) (hj : j ≤ ℓ) :
    Nat.choose (ℓ + 2 - j) (j + 1) =
      Nat.choose (ℓ + 1 - j) (j + 1) + Nat.choose (ℓ + 1 - j) j := by
  rw [show ℓ + 2 - j = (ℓ + 1 - j) + 1 by omega]
  rw [Nat.choose_succ_succ']
  ac_rfl

/-- Closed-form coefficient formula for the path independent-set polynomial. -/
theorem pathIndSetPoly_coeff_closed : ∀ ℓ j : Nat,
    (pathIndSetPoly ℓ).coeff j = (Nat.choose (ℓ + 1 - j) j : ℤ)
  | 0, 0 => by simp [pathIndSetPoly_zero_val]
  | 0, j + 1 => by
      rw [pathIndSetPoly_zero_val]
      simp [Polynomial.coeff_one]
  | 1, 0 => by
      rw [pathIndSetPoly_one_val]
      simp [Polynomial.coeff_one, Polynomial.coeff_X]
  | 1, j + 1 => by
      rw [pathIndSetPoly_one_val]
      cases j with
      | zero => simp [Polynomial.coeff_one, Polynomial.coeff_X]
      | succ j =>
          simp [Polynomial.coeff_one, Polynomial.coeff_X, Nat.choose_eq_zero_of_lt]
  | ℓ + 2, 0 => by
      rw [pathIndSetPoly_recurrence]
      simp only [coeff_add]
      rw [mul_comm X (pathIndSetPoly ℓ), Polynomial.coeff_mul_X_zero]
      rw [pathIndSetPoly_coeff_closed (ℓ + 1) 0]
      simp
  | ℓ + 2, j + 1 => by
      rw [pathIndSetPoly_recurrence]
      simp only [coeff_add]
      rw [mul_comm X (pathIndSetPoly ℓ), Polynomial.coeff_mul_X]
      rw [pathIndSetPoly_coeff_closed (ℓ + 1) (j + 1), pathIndSetPoly_coeff_closed ℓ j]
      by_cases hj : j ≤ ℓ
      · have hrec := choose_pathIndSet_recurrence ℓ j hj
        rw [show ℓ + 1 + 1 - (j + 1) = ℓ + 1 - j by omega]
        rw [show ℓ + 2 + 1 - (j + 1) = ℓ + 2 - j by omega]
        exact_mod_cast hrec.symm
      · have hjgt : ℓ < j := Nat.lt_of_not_ge hj
        have hleft :
            Nat.choose (ℓ + 2 - j) (j + 1) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          omega
        have hfirst :
            Nat.choose (ℓ + 1 - j) (j + 1) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          omega
        have hsecond :
            Nat.choose (ℓ + 1 - j) j = 0 := by
          apply Nat.choose_eq_zero_of_lt
          omega
        simp [hleft, hfirst, hsecond]

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: the path independent-set polynomial has binomial coefficients
    `choose (ℓ + 1 - j) j`, so the `j`-step inverse-rewrite count is read off directly from the
    `j`-th coefficient. This is the closed coefficient form of
    `I_ℓ(t) = Σ_j choose (ℓ + 1 - j) j t^j`.
    thm:pom-path-indset-poly-closed -/
theorem paper_pom_path_indset_poly_closed :
    ∀ ℓ j : Nat, (pathIndSetPoly ℓ).coeff j = (Nat.choose (ℓ + 1 - j) j : ℤ) :=
  pathIndSetPoly_coeff_closed

end Omega
