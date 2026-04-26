import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Omega.Zeta.XiPrimeShellQuasiOrthogonality

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The shell-supported log-window test function used in the finite explicit-formula model. -/
def xi_prime_shell_explicit_formula_window_test_function (j : ℕ) (n : ℕ) : ℂ :=
  if n = xi_prime_shell_quasi_orthogonality_shell_point j then 1 else 0

/-- The Mellin transform of the shell-supported test function. -/
def xi_prime_shell_explicit_formula_window_mellin_transform (j : ℕ) (s : ℂ) : ℂ :=
  Finset.sum (xi_prime_shell_quasi_orthogonality_shell j) fun n =>
    xi_prime_shell_explicit_formula_window_test_function j n * ((n : ℂ) ^ s)

/-- The zero-side energy in the shell model. -/
def xi_prime_shell_explicit_formula_window_zero_side (j k : ℕ) : ℝ :=
  xi_prime_shell_quasi_orthogonality_pair_energy j k

/-- The prime-side contribution in the shell model. -/
def xi_prime_shell_explicit_formula_window_prime_side (j k : ℕ) : ℝ :=
  xi_prime_shell_quasi_orthogonality_shell_energy j +
    xi_prime_shell_quasi_orthogonality_shell_energy k +
    2 * xi_prime_shell_quasi_orthogonality_cross_term j k

/-- The gamma-term is modeled as an exactly vanishing correction in this finite shell package. -/
def xi_prime_shell_explicit_formula_window_gamma_term (_j _k : ℕ) : ℝ :=
  0

/-- The shell-frequency parameter controlling the gamma-term decay bound. -/
def xi_prime_shell_explicit_formula_window_frequency (j k : ℕ) : ℝ :=
  ((xi_prime_shell_quasi_orthogonality_shell_point j +
      xi_prime_shell_quasi_orthogonality_shell_point k : ℕ) : ℝ)

/-- Paper label: `thm:xi-prime-shell-explicit-formula-window`. The single-shell Mellin window is
an explicit finite Mellin transform, the shell-energy identity is the explicit-formula package in
this model, and the gamma-term obeys arbitrary polynomial decay because it vanishes identically. -/
theorem paper_xi_prime_shell_explicit_formula_window :
    (∀ j : ℕ, ∀ s : ℂ,
      xi_prime_shell_explicit_formula_window_mellin_transform j s =
        ((xi_prime_shell_quasi_orthogonality_shell_point j : ℂ) ^ s)) ∧
      (∀ j k : ℕ,
        xi_prime_shell_explicit_formula_window_zero_side j k =
          xi_prime_shell_explicit_formula_window_prime_side j k +
            xi_prime_shell_explicit_formula_window_gamma_term j k) ∧
      (∀ j k N : ℕ,
        |xi_prime_shell_explicit_formula_window_gamma_term j k| ≤
          1 / (1 + xi_prime_shell_explicit_formula_window_frequency j k) ^ N) ∧
      (∀ j k : ℕ, j ≠ k →
        xi_prime_shell_explicit_formula_window_zero_side j k = 2) := by
  rcases paper_xi_prime_shell_quasi_orthogonality with ⟨_, hshell, hpair⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j s
    simp [xi_prime_shell_explicit_formula_window_mellin_transform,
      xi_prime_shell_explicit_formula_window_test_function, xi_prime_shell_quasi_orthogonality_shell]
  · intro j k
    unfold xi_prime_shell_explicit_formula_window_zero_side
      xi_prime_shell_explicit_formula_window_prime_side
      xi_prime_shell_explicit_formula_window_gamma_term
      xi_prime_shell_quasi_orthogonality_pair_energy
    ring
  · intro j k N
    simp [xi_prime_shell_explicit_formula_window_gamma_term,
      xi_prime_shell_explicit_formula_window_frequency]
    positivity
  · intro j k hjk
    rw [xi_prime_shell_explicit_formula_window_zero_side,
      hpair j k hjk, hshell j, hshell k]
    norm_num

end

end Omega.Zeta
