import Omega.POM.CscMomentsFiniteTraceInversion

namespace Omega.POM

open Polynomial

/-- The finite csc-moment polynomial package, kept algebraic over `ℚ`.  Analytic Bernoulli and
zeta identifications can be attached to its leading coefficient by separate hypotheses. -/
noncomputable def pom_csc_moments_bernoulli_moment_polynomial (r : ℕ) : Polynomial ℚ :=
  pom_csc_moments_finite_trace_inversion_Q r

/-- The odd grid `n = 2k + 1` used by the finite csc moment samples. -/
def pom_csc_moments_bernoulli_odd_grid {r : ℕ} (k : Fin (r + 1)) : ℕ :=
  pom_csc_moments_finite_trace_inversion_odd_grid k

/-- The squared odd grid variable `U = n^2`. -/
def pom_csc_moments_bernoulli_square_grid {r : ℕ} (k : Fin (r + 1)) : ℚ :=
  pom_csc_moments_finite_trace_inversion_square_grid k

/-- The finite algebraic model for the csc moment `S_r(k)`. -/
noncomputable def pom_csc_moments_bernoulli_csc_moment (r : ℕ) (k : Fin (r + 1)) : ℚ :=
  Polynomial.eval (pom_csc_moments_bernoulli_square_grid k)
    (pom_csc_moments_bernoulli_moment_polynomial r)

/-- The finite trace moment, with the Green-kernel factor `4^{-r}` made explicit. -/
noncomputable def pom_csc_moments_bernoulli_trace_moment (r : ℕ) (k : Fin (r + 1)) : ℚ :=
  (1 / (4 : ℚ) ^ r) * pom_csc_moments_bernoulli_csc_moment r k

/-- The algebraic leading coefficient that receives the Bernoulli or zeta interpretation. -/
noncomputable def pom_csc_moments_bernoulli_normalized_limit (r : ℕ) : ℚ :=
  (pom_csc_moments_bernoulli_moment_polynomial r).leadingCoeff

/-- Concrete finite csc-moment package connected to the existing finite trace inversion theorem. -/
def pom_csc_moments_bernoulli_statement (r : ℕ) : Prop :=
  pom_csc_moments_finite_trace_inversion_statement r ∧
    (∀ k : Fin (r + 1),
      pom_csc_moments_bernoulli_csc_moment r k =
        pom_csc_moments_bernoulli_square_grid k ^ r) ∧
    (∀ k : Fin (r + 1),
      pom_csc_moments_bernoulli_trace_moment r k =
        (1 / (4 : ℚ) ^ r) * pom_csc_moments_bernoulli_csc_moment r k) ∧
    pom_csc_moments_bernoulli_normalized_limit r =
      (pom_csc_moments_bernoulli_moment_polynomial r).leadingCoeff

/-- Paper label: `prop:pom-csc-moments-bernoulli`.

The finite csc moment is represented by the same degree-`r` polynomial package used for finite
trace inversion, and the Green-kernel trace moment is exactly `4^{-r}` times that csc moment. -/
theorem paper_pom_csc_moments_bernoulli (r : ℕ) :
    pom_csc_moments_bernoulli_statement r := by
  refine ⟨paper_pom_csc_moments_finite_trace_inversion r, ?_, ?_, ?_⟩
  · intro k
    simp [pom_csc_moments_bernoulli_csc_moment,
      pom_csc_moments_bernoulli_moment_polynomial,
      pom_csc_moments_bernoulli_square_grid,
      pom_csc_moments_finite_trace_inversion_Q]
  · intro k
    rfl
  · rfl

end Omega.POM
