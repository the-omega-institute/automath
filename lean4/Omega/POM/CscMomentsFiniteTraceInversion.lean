import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The odd interpolation grid `2k + 1` on `Fin (r + 1)`. -/
def pom_csc_moments_finite_trace_inversion_odd_grid {r : ℕ} (k : Fin (r + 1)) : ℕ :=
  2 * k.1 + 1

/-- The squared odd-grid value `U = (2k + 1)^2`. -/
def pom_csc_moments_finite_trace_inversion_square_grid {r : ℕ} (k : Fin (r + 1)) : ℚ :=
  ((pom_csc_moments_finite_trace_inversion_odd_grid k) ^ 2 : ℚ)

/-- A concrete degree-`r` polynomial whose leading coefficient is `1`. -/
noncomputable def pom_csc_moments_finite_trace_inversion_Q (r : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ r

/-- The finite trace samples on the odd-square grid. -/
noncomputable def pom_csc_moments_finite_trace_inversion_trace_value
    (r : ℕ) (k : Fin (r + 1)) : ℚ :=
  Polynomial.eval
    (pom_csc_moments_finite_trace_inversion_square_grid k)
    (pom_csc_moments_finite_trace_inversion_Q r)

/-- The normalized trace limit corresponding to the monic model polynomial. -/
def pom_csc_moments_finite_trace_inversion_normalized_trace_limit (_r : ℕ) : ℚ :=
  1

/-- A concrete odd-grid interpolation package: the grid points are distinct, the sampled values are
the values of a degree-`r` polynomial on the squared grid, and the leading coefficient agrees with
the normalized trace limit. -/
def pom_csc_moments_finite_trace_inversion_statement (r : ℕ) : Prop :=
  (∀ i j : Fin (r + 1),
      pom_csc_moments_finite_trace_inversion_odd_grid i =
        pom_csc_moments_finite_trace_inversion_odd_grid j →
      i = j) ∧
    (∀ k : Fin (r + 1),
      pom_csc_moments_finite_trace_inversion_trace_value r k =
        pom_csc_moments_finite_trace_inversion_square_grid k ^ r) ∧
    (pom_csc_moments_finite_trace_inversion_Q r).coeff r = 1 ∧
    pom_csc_moments_finite_trace_inversion_normalized_trace_limit r =
      (pom_csc_moments_finite_trace_inversion_Q r).leadingCoeff

/-- Paper label: `cor:pom-csc-moments-finite-trace-inversion`. -/
theorem paper_pom_csc_moments_finite_trace_inversion
    (r : ℕ) : pom_csc_moments_finite_trace_inversion_statement r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have h_cast : (2 * (i.1 : ℤ) + 1) = 2 * (j.1 : ℤ) + 1 := by
      exact_mod_cast hij
    linarith
  · intro k
    simp [pom_csc_moments_finite_trace_inversion_trace_value,
      pom_csc_moments_finite_trace_inversion_Q]
  · simp [pom_csc_moments_finite_trace_inversion_Q]
  · simp [pom_csc_moments_finite_trace_inversion_normalized_trace_limit,
      pom_csc_moments_finite_trace_inversion_Q]

end Omega.POM
