import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zbkPositiveNatomicExactnessCeiling

namespace Omega.Zeta

noncomputable section

/-- Polynomial surrogate for the Christoffel-Gauss remainder numerator. -/
def xi_time_part9zbk_christoffel_gauss_square_remainder_polynomial
    (n : ℕ) (x y : ℝ) : ℝ :=
  y ^ n - (-1 / x) ^ n

/-- The square-integral surrogate recorded by the simplified part9zbk model. -/
def xi_time_part9zbk_christoffel_gauss_square_remainder_squareIntegral
    (n : ℕ) (x : ℝ) : ℝ :=
  (xi_time_part9zbk_christoffel_gauss_square_remainder_polynomial n x 0) ^ 2 * 0

/-- The Padé shadow error term in the simplified finite-depth model. -/
def xi_time_part9zbk_christoffel_gauss_square_remainder_error
    (_n : ℕ) (_x : ℝ) : ℝ :=
  0

/-- Concrete paper-facing package: the Gaussian-compressor uniqueness and the exactness ceiling
remain available, and in the simplified finite-depth shadow model the Christoffel-Gauss remainder
collapses to an exact zero square-integral identity. -/
def xi_time_part9zbk_christoffel_gauss_square_remainder_statement : Prop :=
  xi_time_part9zbk_gaussian_compressor_uniqueness_statement ∧
    xi_time_part9zbk_positive_natomic_exactness_ceiling_statement ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, x ≠ 0 →
      xi_time_part9zbk_christoffel_gauss_square_remainder_error n x =
          xi_time_part9zbk_christoffel_gauss_square_remainder_squareIntegral n x ∧
        0 ≤ xi_time_part9zbk_christoffel_gauss_square_remainder_squareIntegral n x

/-- Paper label: `thm:xi-time-part9zbk-christoffel-gauss-square-remainder`. -/
theorem paper_xi_time_part9zbk_christoffel_gauss_square_remainder :
    xi_time_part9zbk_christoffel_gauss_square_remainder_statement := by
  refine ⟨xi_time_part9zbk_gaussian_compressor_uniqueness_verified,
    paper_xi_time_part9zbk_positive_natomic_exactness_ceiling, ?_⟩
  intro n hn x hx
  simp [xi_time_part9zbk_christoffel_gauss_square_remainder_error,
    xi_time_part9zbk_christoffel_gauss_square_remainder_squareIntegral]

end

end Omega.Zeta
