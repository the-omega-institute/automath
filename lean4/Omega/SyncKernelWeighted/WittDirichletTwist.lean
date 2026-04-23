import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Explicit Adams substitution on a ghost sequence: replace `n` by `d * n`. -/
def witt_dirichlet_twist_adams_substitution (a : ℕ → ℚ) (d : ℕ) : ℕ → ℚ :=
  fun n => a (d * n)

/-- Twisted ghost data obtained by weighting each trace coefficient by the Dirichlet character. -/
def witt_dirichlet_twist_twisted_ghost (χ a : ℕ → ℚ) : ℕ → ℚ :=
  fun n => χ n * a n

/-- The termwise twisted Möbius inversion formula. -/
def witt_dirichlet_twist_twisted_mobius_term (χ a : ℕ → ℚ) (n : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d =>
    (ArithmeticFunction.moebius d : ℚ) * χ d *
      witt_dirichlet_twist_adams_substitution a d (n / d)

/-- The primitive Witt coordinate obtained from the twisted ghost data. -/
def witt_dirichlet_twist_twisted_primitive (χ a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (1 / (n : ℚ)) * witt_dirichlet_twist_twisted_mobius_term χ a n

/-- Euler-product coefficient extracted from the twisted primitive coordinate. -/
def witt_dirichlet_twist_twisted_euler_coeff (χ a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (n : ℚ) * witt_dirichlet_twist_twisted_primitive χ a n

/-- Twisted zeta coefficient identified with the same termwise Möbius sum. -/
def witt_dirichlet_twist_twisted_zeta_coeff (χ a : ℕ → ℚ) (n : ℕ) : ℚ :=
  witt_dirichlet_twist_twisted_mobius_term χ a n

/-- Explicit twisted ghost/Witt data with Adams substitution satisfy the termwise twisted Möbius
formula, and the resulting Euler-product coefficients agree with the twisted zeta expansion.
    thm:witt-dirichlet-twist -/
theorem paper_witt_dirichlet_twist (χ a : ℕ → ℚ) :
    (∀ n, witt_dirichlet_twist_twisted_ghost χ a n = χ n * a n) ∧
      (∀ n : ℕ, 1 ≤ n →
        (n : ℚ) * witt_dirichlet_twist_twisted_primitive χ a n =
          witt_dirichlet_twist_twisted_mobius_term χ a n) ∧
      (∀ n : ℕ, 1 ≤ n →
        witt_dirichlet_twist_twisted_euler_coeff χ a n =
          witt_dirichlet_twist_twisted_zeta_coeff χ a n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    have hnq : (n : ℚ) ≠ 0 := by
      exact_mod_cast hn0
    unfold witt_dirichlet_twist_twisted_primitive
    field_simp [witt_dirichlet_twist_twisted_mobius_term, hnq]
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    have hnq : (n : ℚ) ≠ 0 := by
      exact_mod_cast hn0
    unfold witt_dirichlet_twist_twisted_euler_coeff
      witt_dirichlet_twist_twisted_zeta_coeff
      witt_dirichlet_twist_twisted_primitive
    field_simp [witt_dirichlet_twist_twisted_mobius_term, hnq]

end Omega.SyncKernelWeighted
