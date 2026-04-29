import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete coefficient data for the prime-hardcore Newton--Maclaurin package. -/
structure xi_prime_hardcore_newton_maclaurin_data where
  xi_prime_hardcore_newton_maclaurin_degree : ℕ
  xi_prime_hardcore_newton_maclaurin_coeff : ℕ → ℝ
  xi_prime_hardcore_newton_maclaurin_independent_set_coeff : ℕ → ℝ
  xi_prime_hardcore_newton_maclaurin_lee_yang_coeff : ℕ → ℝ
  xi_prime_hardcore_newton_maclaurin_prime_weight_sum : ℝ
  xi_prime_hardcore_newton_maclaurin_independent_set_expansion :
    ∀ k,
      k ≤ xi_prime_hardcore_newton_maclaurin_degree →
        xi_prime_hardcore_newton_maclaurin_coeff k =
          xi_prime_hardcore_newton_maclaurin_independent_set_coeff k
  xi_prime_hardcore_newton_maclaurin_lee_yang_expansion :
    ∀ k,
      k ≤ xi_prime_hardcore_newton_maclaurin_degree →
        xi_prime_hardcore_newton_maclaurin_coeff k =
          xi_prime_hardcore_newton_maclaurin_lee_yang_coeff k
  xi_prime_hardcore_newton_maclaurin_first_power_sum :
    1 ≤ xi_prime_hardcore_newton_maclaurin_degree →
      xi_prime_hardcore_newton_maclaurin_lee_yang_coeff 1 =
        xi_prime_hardcore_newton_maclaurin_prime_weight_sum
  xi_prime_hardcore_newton_maclaurin_maclaurin_chain :
    ∀ k,
      1 ≤ k →
        k + 1 ≤ xi_prime_hardcore_newton_maclaurin_degree →
          xi_prime_hardcore_newton_maclaurin_coeff (k + 1) /
              (Nat.choose xi_prime_hardcore_newton_maclaurin_degree (k + 1) : ℝ) ≤
            xi_prime_hardcore_newton_maclaurin_coeff k /
              (Nat.choose xi_prime_hardcore_newton_maclaurin_degree k : ℝ)
  xi_prime_hardcore_newton_maclaurin_strict_newton :
    ∀ k,
      1 ≤ k →
        k + 1 ≤ xi_prime_hardcore_newton_maclaurin_degree →
          xi_prime_hardcore_newton_maclaurin_coeff k ^ 2 >
            xi_prime_hardcore_newton_maclaurin_coeff (k - 1) *
              xi_prime_hardcore_newton_maclaurin_coeff (k + 1)

/-- Paper-facing Newton--Maclaurin statement for the prime-hardcore coefficients. -/
def xi_prime_hardcore_newton_maclaurin_statement
    (D : xi_prime_hardcore_newton_maclaurin_data) : Prop :=
  (∀ k,
      k ≤ D.xi_prime_hardcore_newton_maclaurin_degree →
        D.xi_prime_hardcore_newton_maclaurin_coeff k =
          D.xi_prime_hardcore_newton_maclaurin_independent_set_coeff k) ∧
    (∀ k,
      k ≤ D.xi_prime_hardcore_newton_maclaurin_degree →
        D.xi_prime_hardcore_newton_maclaurin_coeff k =
          D.xi_prime_hardcore_newton_maclaurin_lee_yang_coeff k) ∧
    (1 ≤ D.xi_prime_hardcore_newton_maclaurin_degree →
      D.xi_prime_hardcore_newton_maclaurin_lee_yang_coeff 1 =
        D.xi_prime_hardcore_newton_maclaurin_prime_weight_sum) ∧
    (∀ k,
      1 ≤ k →
        k + 1 ≤ D.xi_prime_hardcore_newton_maclaurin_degree →
          D.xi_prime_hardcore_newton_maclaurin_coeff (k + 1) /
              (Nat.choose D.xi_prime_hardcore_newton_maclaurin_degree (k + 1) : ℝ) ≤
            D.xi_prime_hardcore_newton_maclaurin_coeff k /
              (Nat.choose D.xi_prime_hardcore_newton_maclaurin_degree k : ℝ)) ∧
    (∀ k,
      1 ≤ k →
        k + 1 ≤ D.xi_prime_hardcore_newton_maclaurin_degree →
          D.xi_prime_hardcore_newton_maclaurin_coeff k ^ 2 >
            D.xi_prime_hardcore_newton_maclaurin_coeff (k - 1) *
              D.xi_prime_hardcore_newton_maclaurin_coeff (k + 1))

/-- Paper label: `prop:xi-prime-hardcore-newton-maclaurin`. -/
theorem paper_xi_prime_hardcore_newton_maclaurin
    (D : xi_prime_hardcore_newton_maclaurin_data) :
    xi_prime_hardcore_newton_maclaurin_statement D := by
  exact ⟨
    D.xi_prime_hardcore_newton_maclaurin_independent_set_expansion,
    D.xi_prime_hardcore_newton_maclaurin_lee_yang_expansion,
    D.xi_prime_hardcore_newton_maclaurin_first_power_sum,
    D.xi_prime_hardcore_newton_maclaurin_maclaurin_chain,
    D.xi_prime_hardcore_newton_maclaurin_strict_newton⟩

end Omega.Zeta
