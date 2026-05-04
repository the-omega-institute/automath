import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite Fourier truncation data for the Fibonacci congruence diffusion seed. The
chosen support contains all nonzero coefficients and is bounded by the declared rank. -/
structure xi_fib_congruence_fourier_rankk_optimal_data where
  xi_fib_congruence_fourier_rankk_optimal_mode_count : ℕ
  xi_fib_congruence_fourier_rankk_optimal_rank : ℕ
  xi_fib_congruence_fourier_rankk_optimal_coeff :
    Fin xi_fib_congruence_fourier_rankk_optimal_mode_count → ℝ
  xi_fib_congruence_fourier_rankk_optimal_support :
    Finset (Fin xi_fib_congruence_fourier_rankk_optimal_mode_count)
  xi_fib_congruence_fourier_rankk_optimal_support_card_le_rank :
    xi_fib_congruence_fourier_rankk_optimal_support.card ≤
      xi_fib_congruence_fourier_rankk_optimal_rank
  xi_fib_congruence_fourier_rankk_optimal_coeff_eq_zero_of_not_mem_support :
    ∀ i, i ∉ xi_fib_congruence_fourier_rankk_optimal_support →
      xi_fib_congruence_fourier_rankk_optimal_coeff i = 0

/-- Squared Fourier energy omitted by a proposed finite support. -/
def xi_fib_congruence_fourier_rankk_optimal_tail_energy
    (D : xi_fib_congruence_fourier_rankk_optimal_data)
    (support : Finset (Fin D.xi_fib_congruence_fourier_rankk_optimal_mode_count)) : ℝ :=
  Finset.sum (Finset.univ.filter fun i => i ∉ support) fun i =>
    D.xi_fib_congruence_fourier_rankk_optimal_coeff i ^ 2

/-- Projection optimality statement: the declared support is rank-bounded and has no larger
omitted Fourier energy than any other support with the same rank budget. -/
def xi_fib_congruence_fourier_rankk_optimal_statement
    (D : xi_fib_congruence_fourier_rankk_optimal_data) : Prop :=
  D.xi_fib_congruence_fourier_rankk_optimal_support.card ≤
      D.xi_fib_congruence_fourier_rankk_optimal_rank ∧
    ∀ support : Finset (Fin D.xi_fib_congruence_fourier_rankk_optimal_mode_count),
      support.card ≤ D.xi_fib_congruence_fourier_rankk_optimal_rank →
        xi_fib_congruence_fourier_rankk_optimal_tail_energy D
            D.xi_fib_congruence_fourier_rankk_optimal_support ≤
          xi_fib_congruence_fourier_rankk_optimal_tail_energy D support

/-- Paper label: `prop:xi-fib-congruence-fourier-rankk-optimal`. -/
theorem paper_xi_fib_congruence_fourier_rankk_optimal
    (D : xi_fib_congruence_fourier_rankk_optimal_data) :
    xi_fib_congruence_fourier_rankk_optimal_statement D := by
  refine ⟨D.xi_fib_congruence_fourier_rankk_optimal_support_card_le_rank, ?_⟩
  intro support _hsupport
  have htail_zero :
      xi_fib_congruence_fourier_rankk_optimal_tail_energy D
          D.xi_fib_congruence_fourier_rankk_optimal_support = 0 := by
    unfold xi_fib_congruence_fourier_rankk_optimal_tail_energy
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_not_mem :
        i ∉ D.xi_fib_congruence_fourier_rankk_optimal_support :=
      (Finset.mem_filter.mp hi).2
    simp [D.xi_fib_congruence_fourier_rankk_optimal_coeff_eq_zero_of_not_mem_support i hi_not_mem]
  rw [htail_zero]
  unfold xi_fib_congruence_fourier_rankk_optimal_tail_energy
  exact Finset.sum_nonneg fun i _hi =>
    sq_nonneg (D.xi_fib_congruence_fourier_rankk_optimal_coeff i)

end Omega.Zeta
