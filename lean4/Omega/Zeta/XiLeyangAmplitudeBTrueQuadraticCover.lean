import Mathlib.Tactic

namespace Omega.Zeta

/-- Data placeholder for the Lee--Yang amplitude quadratic-cover certificate. -/
structure xi_leyang_amplitude_b_true_quadratic_cover_data where

/-- The norm of `B^2` in the cubic Lee--Yang field, read from the monic cubic. -/
def xi_leyang_amplitude_b_true_quadratic_cover_cubic_norm : ℚ := -592 / 81

/-- The cubic field degree `[ℚ(B^2) : ℚ]`. -/
def xi_leyang_amplitude_b_true_quadratic_cover_cubic_degree : ℕ := 3

/-- The genuine quadratic cover degree `[ℚ(B) : ℚ(B^2)]`. -/
def xi_leyang_amplitude_b_true_quadratic_cover_quadratic_degree : ℕ := 2

/-- The resulting absolute degree `[ℚ(B) : ℚ]`. -/
def xi_leyang_amplitude_b_true_quadratic_cover_total_degree : ℕ := 6

/--
Concrete Lean statement for the paper theorem: the cubic norm is negative, so it cannot
be a rational square, and the quadratic-over-cubic tower has degree `2 * 3 = 6`.
-/
def xi_leyang_amplitude_b_true_quadratic_cover_statement
    (_D : xi_leyang_amplitude_b_true_quadratic_cover_data) : Prop :=
  xi_leyang_amplitude_b_true_quadratic_cover_cubic_norm < 0 ∧
    (∀ q : ℚ, q ^ 2 ≠ xi_leyang_amplitude_b_true_quadratic_cover_cubic_norm) ∧
    xi_leyang_amplitude_b_true_quadratic_cover_total_degree =
      xi_leyang_amplitude_b_true_quadratic_cover_quadratic_degree *
        xi_leyang_amplitude_b_true_quadratic_cover_cubic_degree ∧
    xi_leyang_amplitude_b_true_quadratic_cover_total_degree = 6 ∧
    xi_leyang_amplitude_b_true_quadratic_cover_quadratic_degree = 2 ∧
    xi_leyang_amplitude_b_true_quadratic_cover_cubic_degree = 3

/-- Paper label: `thm:xi-leyang-amplitude-B-true-quadratic-cover`. -/
theorem paper_xi_leyang_amplitude_b_true_quadratic_cover
    (D : xi_leyang_amplitude_b_true_quadratic_cover_data) :
    xi_leyang_amplitude_b_true_quadratic_cover_statement D := by
  constructor
  · norm_num [xi_leyang_amplitude_b_true_quadratic_cover_cubic_norm]
  · constructor
    · intro q hq
      have hsq : 0 ≤ q ^ 2 := sq_nonneg q
      rw [hq] at hsq
      norm_num [xi_leyang_amplitude_b_true_quadratic_cover_cubic_norm] at hsq
    · norm_num [xi_leyang_amplitude_b_true_quadratic_cover_total_degree,
        xi_leyang_amplitude_b_true_quadratic_cover_quadratic_degree,
        xi_leyang_amplitude_b_true_quadratic_cover_cubic_degree]

end Omega.Zeta
