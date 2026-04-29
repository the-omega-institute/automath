import Mathlib.Tactic

namespace Omega.Zeta

/-- A row-sum tail estimate transfers to any scalar controlled by that tail. -/
lemma xi_hellinger_quasi_orthogonal_phase_convergence_of_tail_bound
    (tail f : ℕ → ℝ) (center : ℝ)
    (h_tail : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |tail n| < eps)
    (h_bound : ∀ n : ℕ, |f n - center| ≤ tail n) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n - center| < eps := by
  intro eps h_eps
  obtain ⟨N, hN⟩ := h_tail eps h_eps
  refine ⟨N, ?_⟩
  intro n hn
  exact lt_of_le_of_lt (le_trans (h_bound n) (le_abs_self (tail n))) (hN n hn)

/-- Paper label: `cor:xi-hellinger-quasi-orthogonal-phase`. -/
theorem paper_xi_hellinger_quasi_orthogonal_phase
    (tail lambdaMin lambdaMax detG entropy : ℕ → ℝ)
    (h_tail : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |tail n| < eps)
    (h_min : ∀ n : ℕ, |lambdaMin n - 1| ≤ tail n)
    (h_max : ∀ n : ℕ, |lambdaMax n - 1| ≤ tail n)
    (h_det : ∀ n : ℕ, |detG n - 1| ≤ tail n)
    (h_entropy : ∀ n : ℕ, |entropy n| ≤ tail n) :
    (∀ eps : ℝ, 0 < eps →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |lambdaMin n - 1| < eps) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |lambdaMax n - 1| < eps) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |detG n - 1| < eps) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |entropy n| < eps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xi_hellinger_quasi_orthogonal_phase_convergence_of_tail_bound
      tail lambdaMin 1 h_tail h_min
  · exact xi_hellinger_quasi_orthogonal_phase_convergence_of_tail_bound
      tail lambdaMax 1 h_tail h_max
  · exact xi_hellinger_quasi_orthogonal_phase_convergence_of_tail_bound
      tail detG 1 h_tail h_det
  · have h_entropy_bound : ∀ n : ℕ, |entropy n - 0| ≤ tail n := by
      intro n
      simpa using h_entropy n
    simpa using
      (xi_hellinger_quasi_orthogonal_phase_convergence_of_tail_bound
        tail entropy 0 h_tail h_entropy_bound)

end Omega.Zeta
