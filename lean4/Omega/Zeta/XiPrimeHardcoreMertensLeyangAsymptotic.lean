import Mathlib
import Omega.Zeta.XiPrimeHardcoreNormalizationConstant

namespace Omega.Zeta

noncomputable section

open Filter

/-- Concrete Mertens/Lee--Yang data for the prime-hardcore asymptotic package.  The three
convergent scalar factors are kept as actual sequences, and the hardcore factor is tied to the
normalization constant proved in `XiPrimeHardcoreNormalizationConstant`. -/
structure xi_prime_hardcore_mertens_leyang_asymptotic_data where
  xi_prime_hardcore_mertens_leyang_asymptotic_t : ℝ
  xi_prime_hardcore_mertens_leyang_asymptotic_mertensProduct : ℕ → ℝ
  xi_prime_hardcore_mertens_leyang_asymptotic_leyangEulerFactor : ℕ → ℝ
  xi_prime_hardcore_mertens_leyang_asymptotic_mertensLimit : ℝ
  xi_prime_hardcore_mertens_leyang_asymptotic_leyangEulerLimit : ℝ
  xi_prime_hardcore_mertens_leyang_asymptotic_t_pos :
    0 < xi_prime_hardcore_mertens_leyang_asymptotic_t
  xi_prime_hardcore_mertens_leyang_asymptotic_mertens_asymptotic :
    Tendsto xi_prime_hardcore_mertens_leyang_asymptotic_mertensProduct atTop
      (nhds xi_prime_hardcore_mertens_leyang_asymptotic_mertensLimit)
  xi_prime_hardcore_mertens_leyang_asymptotic_leyang_euler_converges :
    Tendsto xi_prime_hardcore_mertens_leyang_asymptotic_leyangEulerFactor atTop
      (nhds xi_prime_hardcore_mertens_leyang_asymptotic_leyangEulerLimit)

namespace xi_prime_hardcore_mertens_leyang_asymptotic_data

/-- The finite prime-hardcore amplitude after Mertens normalization and Lee--Yang correction. -/
def xi_prime_hardcore_mertens_leyang_asymptotic_amplitude
    (D : xi_prime_hardcore_mertens_leyang_asymptotic_data) (N : ℕ) : ℝ :=
  D.xi_prime_hardcore_mertens_leyang_asymptotic_mertensProduct N *
    D.xi_prime_hardcore_mertens_leyang_asymptotic_leyangEulerFactor N *
      xi_prime_hardcore_normalization_constant_ratio
        D.xi_prime_hardcore_mertens_leyang_asymptotic_t N

/-- The limiting Mertens/Lee--Yang/hardcore constant. -/
def xi_prime_hardcore_mertens_leyang_asymptotic_limit
    (D : xi_prime_hardcore_mertens_leyang_asymptotic_data) : ℝ :=
  D.xi_prime_hardcore_mertens_leyang_asymptotic_mertensLimit *
    D.xi_prime_hardcore_mertens_leyang_asymptotic_leyangEulerLimit *
      xi_prime_hardcore_normalization_constant_delta
        D.xi_prime_hardcore_mertens_leyang_asymptotic_t

/-- Paper-facing statement: the packaged Mertens product, Lee--Yang Euler factor, and hardcore
normalization converge to the product of their limiting constants, with the hardcore limit positive.
-/
def xi_prime_hardcore_mertens_leyang_asymptotic_statement
    (D : xi_prime_hardcore_mertens_leyang_asymptotic_data) : Prop :=
  Tendsto D.xi_prime_hardcore_mertens_leyang_asymptotic_amplitude atTop
      (nhds D.xi_prime_hardcore_mertens_leyang_asymptotic_limit) ∧
    0 < xi_prime_hardcore_normalization_constant_delta
      D.xi_prime_hardcore_mertens_leyang_asymptotic_t

end xi_prime_hardcore_mertens_leyang_asymptotic_data

open xi_prime_hardcore_mertens_leyang_asymptotic_data

/-- Paper label: `thm:xi-prime-hardcore-mertens-leyang-asymptotic`. -/
theorem paper_xi_prime_hardcore_mertens_leyang_asymptotic
    (D : xi_prime_hardcore_mertens_leyang_asymptotic_data) :
    xi_prime_hardcore_mertens_leyang_asymptotic_statement D := by
  rcases paper_xi_prime_hardcore_normalization_constant
      D.xi_prime_hardcore_mertens_leyang_asymptotic_t_pos with
    ⟨_, hHardcoreTendsto, hHardcorePos, _⟩
  refine ⟨?_, hHardcorePos⟩
  unfold xi_prime_hardcore_mertens_leyang_asymptotic_amplitude
  unfold xi_prime_hardcore_mertens_leyang_asymptotic_limit
  exact
    (D.xi_prime_hardcore_mertens_leyang_asymptotic_mertens_asymptotic.mul
      D.xi_prime_hardcore_mertens_leyang_asymptotic_leyang_euler_converges).mul
        hHardcoreTendsto

end

end Omega.Zeta
