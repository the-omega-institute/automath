import Mathlib.Tactic
import Omega.Zeta.XiTimePart9yZGInfiniteProductPositivity
import Omega.Zeta.XiTimePart9yZGScalarPrimeRecursion

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete prefix data for the prime-indexed `ZG` matrix recursion and density tail. -/
structure xi_time_part62dgd_zg_density_prime_jfraction_positive_data where
  xi_time_part62dgd_zg_density_prime_jfraction_positive_p : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_A : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_B : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_r : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_s : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_delta : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_density : ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_tail : ℕ → ℝ
  xi_time_part62dgd_zg_density_prime_jfraction_positive_p_pos :
    ∀ n, 1 ≤ n → 0 < xi_time_part62dgd_zg_density_prime_jfraction_positive_p n
  xi_time_part62dgd_zg_density_prime_jfraction_positive_A_zero :
    xi_time_part62dgd_zg_density_prime_jfraction_positive_A 0 = 1
  xi_time_part62dgd_zg_density_prime_jfraction_positive_B_zero :
    xi_time_part62dgd_zg_density_prime_jfraction_positive_B 0 = 0
  xi_time_part62dgd_zg_density_prime_jfraction_positive_matrix_step :
    ∀ n, 1 ≤ n →
      xi_time_part62dgd_zg_density_prime_jfraction_positive_A n =
          xi_time_part62dgd_zg_density_prime_jfraction_positive_p n /
              (xi_time_part62dgd_zg_density_prime_jfraction_positive_p n + 1) *
            (xi_time_part62dgd_zg_density_prime_jfraction_positive_A (n - 1) +
              xi_time_part62dgd_zg_density_prime_jfraction_positive_B (n - 1)) ∧
        xi_time_part62dgd_zg_density_prime_jfraction_positive_B n =
          (1 / (xi_time_part62dgd_zg_density_prime_jfraction_positive_p n + 1)) *
            xi_time_part62dgd_zg_density_prime_jfraction_positive_A (n - 1)
  xi_time_part62dgd_zg_density_prime_jfraction_positive_ratio_def :
    ∀ n, 1 ≤ n →
      xi_time_part62dgd_zg_density_prime_jfraction_positive_r n =
        xi_time_part62dgd_zg_density_prime_jfraction_positive_B n /
          xi_time_part62dgd_zg_density_prime_jfraction_positive_A n
  xi_time_part62dgd_zg_density_prime_jfraction_positive_s_zero :
    xi_time_part62dgd_zg_density_prime_jfraction_positive_s 0 = 1
  xi_time_part62dgd_zg_density_prime_jfraction_positive_s_step :
    ∀ n,
      xi_time_part62dgd_zg_density_prime_jfraction_positive_s (n + 1) =
        xi_time_part62dgd_zg_density_prime_jfraction_positive_s n *
          (1 -
            xi_time_part62dgd_zg_density_prime_jfraction_positive_r n /
              ((xi_time_part62dgd_zg_density_prime_jfraction_positive_p (n + 1) + 1) *
                (1 + xi_time_part62dgd_zg_density_prime_jfraction_positive_r n)))
  xi_time_part62dgd_zg_density_prime_jfraction_positive_r_nonneg :
    ∀ n, 0 ≤ xi_time_part62dgd_zg_density_prime_jfraction_positive_r n
  xi_time_part62dgd_zg_density_prime_jfraction_positive_r_small :
    ∀ n,
      xi_time_part62dgd_zg_density_prime_jfraction_positive_r n ≤
        1 / xi_time_part62dgd_zg_density_prime_jfraction_positive_p (n + 1)
  xi_time_part62dgd_zg_density_prime_jfraction_positive_density_pos :
    0 < xi_time_part62dgd_zg_density_prime_jfraction_positive_density
  xi_time_part62dgd_zg_density_prime_jfraction_positive_density_lt_one :
    xi_time_part62dgd_zg_density_prime_jfraction_positive_density < 1
  xi_time_part62dgd_zg_density_prime_jfraction_positive_tail_bound :
    ∀ n, 1 ≤ n →
      0 <
          xi_time_part62dgd_zg_density_prime_jfraction_positive_delta n -
            xi_time_part62dgd_zg_density_prime_jfraction_positive_density ∧
        xi_time_part62dgd_zg_density_prime_jfraction_positive_delta n -
            xi_time_part62dgd_zg_density_prime_jfraction_positive_density ≤
          xi_time_part62dgd_zg_density_prime_jfraction_positive_delta n *
            xi_time_part62dgd_zg_density_prime_jfraction_positive_tail n

/-- Paper-facing certificate for the ratio recurrence, finite products, and density tail. -/
def xi_time_part62dgd_zg_density_prime_jfraction_positive_statement
    (D : xi_time_part62dgd_zg_density_prime_jfraction_positive_data) : Prop :=
  (D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r 1 =
      1 / D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p 1 ∧
    ∀ n, 1 ≤ n →
      D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r (n + 1) =
        1 /
          (D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p (n + 1) *
            (1 + D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r n))) ∧
    (∀ N,
      D.xi_time_part62dgd_zg_density_prime_jfraction_positive_s N =
        (Finset.range N).prod fun n =>
          (1 -
            D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r n /
              ((D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p (n + 1) + 1) *
                (1 + D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r n)))) ∧
      (∀ N,
        0 <
          (Finset.range N).prod fun n =>
            (1 -
              D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r n /
                ((D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p (n + 1) + 1) *
                  (1 + D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r n)))) ∧
        0 < D.xi_time_part62dgd_zg_density_prime_jfraction_positive_density ∧
          D.xi_time_part62dgd_zg_density_prime_jfraction_positive_density < 1 ∧
          ∀ n, 1 ≤ n →
            0 <
                D.xi_time_part62dgd_zg_density_prime_jfraction_positive_delta n -
                  D.xi_time_part62dgd_zg_density_prime_jfraction_positive_density ∧
              D.xi_time_part62dgd_zg_density_prime_jfraction_positive_delta n -
                  D.xi_time_part62dgd_zg_density_prime_jfraction_positive_density ≤
                D.xi_time_part62dgd_zg_density_prime_jfraction_positive_delta n *
                  D.xi_time_part62dgd_zg_density_prime_jfraction_positive_tail n

/-- Paper label: `thm:xi-time-part62dgd-zg-density-prime-jfraction-positive`. -/
theorem paper_xi_time_part62dgd_zg_density_prime_jfraction_positive
    (D : xi_time_part62dgd_zg_density_prime_jfraction_positive_data) :
    xi_time_part62dgd_zg_density_prime_jfraction_positive_statement D := by
  rcases
      paper_xi_time_part9y_zg_scalar_prime_recursion
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_A
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_B
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p_pos
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_A_zero
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_B_zero
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_matrix_step
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_ratio_def with
    ⟨hr_one, hr_step⟩
  rcases
      paper_xi_time_part9y_zg_infinite_product_positivity
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_s
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_s_step
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_s_zero
        (fun n =>
          D.xi_time_part62dgd_zg_density_prime_jfraction_positive_p_pos (n + 1) (by omega))
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r_nonneg
        D.xi_time_part62dgd_zg_density_prime_jfraction_positive_r_small with
    ⟨hs_product, hs_positive⟩
  exact
    ⟨⟨hr_one, hr_step⟩, hs_product, hs_positive,
      D.xi_time_part62dgd_zg_density_prime_jfraction_positive_density_pos,
      D.xi_time_part62dgd_zg_density_prime_jfraction_positive_density_lt_one,
      D.xi_time_part62dgd_zg_density_prime_jfraction_positive_tail_bound⟩

end Omega.Zeta
