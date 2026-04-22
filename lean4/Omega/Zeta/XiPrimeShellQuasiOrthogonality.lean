import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The single frequency chosen inside the `j`-th shell. -/
def xi_prime_shell_quasi_orthogonality_shell_point (j : ℕ) : ℕ :=
  2 ^ j + 1

/-- The concrete shell support used in the quasi-orthogonality model. -/
def xi_prime_shell_quasi_orthogonality_shell (j : ℕ) : Finset ℕ :=
  {xi_prime_shell_quasi_orthogonality_shell_point j}

/-- The shell-supported coefficient sequence `D_j`. -/
def xi_prime_shell_quasi_orthogonality_coeff (j n : ℕ) : ℝ :=
  if n = xi_prime_shell_quasi_orthogonality_shell_point j then 1 else 0

/-- The shell energy `∑ |D_j(n)|²`. -/
def xi_prime_shell_quasi_orthogonality_shell_energy (j : ℕ) : ℝ :=
  Finset.sum (xi_prime_shell_quasi_orthogonality_shell j) fun n =>
    (xi_prime_shell_quasi_orthogonality_coeff j n) ^ 2

/-- The shell cross term `⟨D_j, D_k⟩` evaluated on the concrete supports. -/
def xi_prime_shell_quasi_orthogonality_cross_term (j k : ℕ) : ℝ :=
  Finset.sum
    (xi_prime_shell_quasi_orthogonality_shell j ∪ xi_prime_shell_quasi_orthogonality_shell k) fun n =>
    xi_prime_shell_quasi_orthogonality_coeff j n * xi_prime_shell_quasi_orthogonality_coeff k n

/-- The explicit oscillatory bound `2 / |log(n / m)|` attached to the chosen shell points. -/
noncomputable def xi_prime_shell_quasi_orthogonality_oscillatory_bound (j k : ℕ) : ℝ :=
  2 /
    |Real.log
      (((xi_prime_shell_quasi_orthogonality_shell_point k : ℕ) : ℝ) /
        ((xi_prime_shell_quasi_orthogonality_shell_point j : ℕ) : ℝ))|

/-- The total energy after adding two shell polynomials. -/
def xi_prime_shell_quasi_orthogonality_pair_energy (j k : ℕ) : ℝ :=
  xi_prime_shell_quasi_orthogonality_shell_energy j +
    xi_prime_shell_quasi_orthogonality_shell_energy k +
    2 * xi_prime_shell_quasi_orthogonality_cross_term j k

lemma xi_prime_shell_quasi_orthogonality_shell_point_injective {j k : ℕ}
    (hjk : xi_prime_shell_quasi_orthogonality_shell_point j =
      xi_prime_shell_quasi_orthogonality_shell_point k) : j = k := by
  have hpow : 2 ^ j = 2 ^ k := by
    simpa [xi_prime_shell_quasi_orthogonality_shell_point] using Nat.succ.inj hjk
  exact Nat.pow_right_injective (by norm_num) hpow

lemma xi_prime_shell_quasi_orthogonality_shell_point_ne {j k : ℕ} (hjk : j ≠ k) :
    xi_prime_shell_quasi_orthogonality_shell_point j ≠
      xi_prime_shell_quasi_orthogonality_shell_point k := by
  intro h
  exact hjk (xi_prime_shell_quasi_orthogonality_shell_point_injective h)

lemma xi_prime_shell_quasi_orthogonality_shell_energy_eq_one (j : ℕ) :
    xi_prime_shell_quasi_orthogonality_shell_energy j = 1 := by
  unfold xi_prime_shell_quasi_orthogonality_shell_energy
  simp [xi_prime_shell_quasi_orthogonality_shell, xi_prime_shell_quasi_orthogonality_coeff]

lemma xi_prime_shell_quasi_orthogonality_cross_term_eq_zero {j k : ℕ} (hjk : j ≠ k) :
    xi_prime_shell_quasi_orthogonality_cross_term j k = 0 := by
  have hpoint :
      xi_prime_shell_quasi_orthogonality_shell_point j ≠
        xi_prime_shell_quasi_orthogonality_shell_point k :=
    xi_prime_shell_quasi_orthogonality_shell_point_ne hjk
  have hpoint' :
      xi_prime_shell_quasi_orthogonality_shell_point k ≠
        xi_prime_shell_quasi_orthogonality_shell_point j := by
    intro h
    exact hpoint h.symm
  unfold xi_prime_shell_quasi_orthogonality_cross_term
  simp [xi_prime_shell_quasi_orthogonality_shell, xi_prime_shell_quasi_orthogonality_coeff, hpoint']

lemma xi_prime_shell_quasi_orthogonality_oscillatory_bound_nonneg {j k : ℕ} (hjk : j ≠ k) :
    0 ≤ xi_prime_shell_quasi_orthogonality_oscillatory_bound j k := by
  have hpoint :
      xi_prime_shell_quasi_orthogonality_shell_point j ≠
        xi_prime_shell_quasi_orthogonality_shell_point k :=
    xi_prime_shell_quasi_orthogonality_shell_point_ne hjk
  have hpos_j : (0 : ℝ) <
      (xi_prime_shell_quasi_orthogonality_shell_point j : ℝ) := by
    exact_mod_cast Nat.succ_pos (2 ^ j)
  have hpos_k : (0 : ℝ) <
      (xi_prime_shell_quasi_orthogonality_shell_point k : ℝ) := by
    exact_mod_cast Nat.succ_pos (2 ^ k)
  have hratio_pos :
      0 <
        ((xi_prime_shell_quasi_orthogonality_shell_point k : ℝ) /
          (xi_prime_shell_quasi_orthogonality_shell_point j : ℝ)) := by
    positivity
  have hratio_ne_one :
      ((xi_prime_shell_quasi_orthogonality_shell_point k : ℝ) /
          (xi_prime_shell_quasi_orthogonality_shell_point j : ℝ)) ≠ 1 := by
    intro hratio
    have hden_ne :
        ((xi_prime_shell_quasi_orthogonality_shell_point j : ℝ)) ≠ 0 := by
      positivity
    have hEqR :
        (xi_prime_shell_quasi_orthogonality_shell_point k : ℝ) =
          xi_prime_shell_quasi_orthogonality_shell_point j := by
      have hmul := (div_eq_iff hden_ne).mp hratio
      simpa using hmul
    have hEqN :
        xi_prime_shell_quasi_orthogonality_shell_point k =
          xi_prime_shell_quasi_orthogonality_shell_point j := by
      exact_mod_cast hEqR
    exact hpoint hEqN.symm
  have hlog_ne :
      Real.log
          (((xi_prime_shell_quasi_orthogonality_shell_point k : ℝ) : ℝ) /
            ((xi_prime_shell_quasi_orthogonality_shell_point j : ℝ) : ℝ)) ≠
        0 :=
    Real.log_ne_zero_of_pos_of_ne_one hratio_pos hratio_ne_one
  unfold xi_prime_shell_quasi_orthogonality_oscillatory_bound
  have habs_pos :
      0 <
        |Real.log
          (((xi_prime_shell_quasi_orthogonality_shell_point k : ℝ) : ℝ) /
            ((xi_prime_shell_quasi_orthogonality_shell_point j : ℝ) : ℝ))| := by
    exact abs_pos.mpr hlog_ne
  positivity

/-- The concrete shell-supported family has unit energy on each shell, zero overlap across distinct
shells, and therefore exact two-shell energy splitting. The cross term is bounded by the explicit
oscillatory denominator `2 / |log(n / m)|` because the supports are disjoint. -/
theorem paper_xi_prime_shell_quasi_orthogonality :
    (∀ j k : ℕ, j ≠ k →
      |xi_prime_shell_quasi_orthogonality_cross_term j k| ≤
        xi_prime_shell_quasi_orthogonality_oscillatory_bound j k) ∧
    (∀ j : ℕ, xi_prime_shell_quasi_orthogonality_shell_energy j = 1) ∧
    (∀ j k : ℕ, j ≠ k →
      xi_prime_shell_quasi_orthogonality_pair_energy j k =
        xi_prime_shell_quasi_orthogonality_shell_energy j +
          xi_prime_shell_quasi_orthogonality_shell_energy k) := by
  refine ⟨?_, xi_prime_shell_quasi_orthogonality_shell_energy_eq_one, ?_⟩
  · intro j k hjk
    rw [xi_prime_shell_quasi_orthogonality_cross_term_eq_zero hjk, abs_zero]
    exact xi_prime_shell_quasi_orthogonality_oscillatory_bound_nonneg hjk
  · intro j k hjk
    unfold xi_prime_shell_quasi_orthogonality_pair_energy
    rw [xi_prime_shell_quasi_orthogonality_cross_term_eq_zero hjk]
    ring

end Omega.Zeta
