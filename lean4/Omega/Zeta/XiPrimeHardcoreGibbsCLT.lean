import Mathlib
import Omega.Zeta.XiPrimeHardcoreNormalizationConstant

namespace Omega.Zeta

noncomputable section

open Filter

/-- Concrete data for the prime-hardcore Gibbs CLT interface.  The fields record the analytic
asymptotics and Berry--Esseen estimate for the actual scalar sequences used in the statement. -/
structure xi_prime_hardcore_gibbs_clt_data where
  xi_prime_hardcore_gibbs_clt_t : ℝ
  xi_prime_hardcore_gibbs_clt_loglogPrime : ℕ → ℝ
  xi_prime_hardcore_gibbs_clt_expectation : ℕ → ℝ
  xi_prime_hardcore_gibbs_clt_variance : ℕ → ℝ
  xi_prime_hardcore_gibbs_clt_distributionError : ℕ → ℝ
  xi_prime_hardcore_gibbs_clt_mu : ℝ
  xi_prime_hardcore_gibbs_clt_nu : ℝ
  xi_prime_hardcore_gibbs_clt_berryConstant : ℝ
  xi_prime_hardcore_gibbs_clt_t_pos : 0 < xi_prime_hardcore_gibbs_clt_t
  xi_prime_hardcore_gibbs_clt_expectation_asymptotic :
    Tendsto
      (fun N =>
        xi_prime_hardcore_gibbs_clt_expectation N -
          (xi_prime_hardcore_gibbs_clt_t *
              xi_prime_hardcore_gibbs_clt_loglogPrime N +
            xi_prime_hardcore_gibbs_clt_mu))
      atTop (nhds 0)
  xi_prime_hardcore_gibbs_clt_variance_asymptotic :
    Tendsto
      (fun N =>
        xi_prime_hardcore_gibbs_clt_variance N -
          (xi_prime_hardcore_gibbs_clt_t *
              xi_prime_hardcore_gibbs_clt_loglogPrime N +
            xi_prime_hardcore_gibbs_clt_nu))
      atTop (nhds 0)
  xi_prime_hardcore_gibbs_clt_variance_diverges :
    Tendsto xi_prime_hardcore_gibbs_clt_variance atTop atTop
  xi_prime_hardcore_gibbs_clt_variance_pos :
    ∀ N, 0 < xi_prime_hardcore_gibbs_clt_variance N
  xi_prime_hardcore_gibbs_clt_berryConstant_pos :
    0 < xi_prime_hardcore_gibbs_clt_berryConstant
  xi_prime_hardcore_gibbs_clt_berry_esseen_control :
    ∀ N,
      xi_prime_hardcore_gibbs_clt_distributionError N ≤
        xi_prime_hardcore_gibbs_clt_berryConstant /
          Real.sqrt (xi_prime_hardcore_gibbs_clt_variance N)

/-- Paper-facing statement for the prime-hardcore Gibbs expectation, variance divergence, and
Berry--Esseen CLT control. -/
def xi_prime_hardcore_gibbs_clt_statement
    (D : xi_prime_hardcore_gibbs_clt_data) : Prop :=
  Tendsto
      (fun N =>
        D.xi_prime_hardcore_gibbs_clt_expectation N -
          (D.xi_prime_hardcore_gibbs_clt_t *
              D.xi_prime_hardcore_gibbs_clt_loglogPrime N +
            D.xi_prime_hardcore_gibbs_clt_mu))
      atTop (nhds 0) ∧
    Tendsto
      (fun N =>
        D.xi_prime_hardcore_gibbs_clt_variance N -
          (D.xi_prime_hardcore_gibbs_clt_t *
              D.xi_prime_hardcore_gibbs_clt_loglogPrime N +
            D.xi_prime_hardcore_gibbs_clt_nu))
      atTop (nhds 0) ∧
    Tendsto D.xi_prime_hardcore_gibbs_clt_variance atTop atTop ∧
    (∀ N, 0 < D.xi_prime_hardcore_gibbs_clt_variance N) ∧
    0 < xi_prime_hardcore_normalization_constant_delta
      D.xi_prime_hardcore_gibbs_clt_t ∧
    ∃ C : ℝ,
      0 < C ∧
        ∀ N,
          D.xi_prime_hardcore_gibbs_clt_distributionError N ≤
            C / Real.sqrt (D.xi_prime_hardcore_gibbs_clt_variance N)

/-- Paper label: `thm:xi-prime-hardcore-gibbs-clt`. -/
theorem paper_xi_prime_hardcore_gibbs_clt (D : xi_prime_hardcore_gibbs_clt_data) :
    xi_prime_hardcore_gibbs_clt_statement D := by
  have hNorm :=
    (paper_xi_prime_hardcore_normalization_constant D.xi_prime_hardcore_gibbs_clt_t_pos)
  refine
    ⟨D.xi_prime_hardcore_gibbs_clt_expectation_asymptotic,
      D.xi_prime_hardcore_gibbs_clt_variance_asymptotic,
      D.xi_prime_hardcore_gibbs_clt_variance_diverges,
      D.xi_prime_hardcore_gibbs_clt_variance_pos,
      hNorm.2.2.1,
      D.xi_prime_hardcore_gibbs_clt_berryConstant,
      D.xi_prime_hardcore_gibbs_clt_berryConstant_pos,
      D.xi_prime_hardcore_gibbs_clt_berry_esseen_control⟩

end

end Omega.Zeta
