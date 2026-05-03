import Omega.Zeta.PoissonCauchyMixtureT4OptimalityRigidity

namespace Omega.Zeta

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Concrete data for the Cauchy--Poisson KL rigidity corollary. -/
structure xi_cauchy_poisson_kl_rigidity_data where
  xi_cauchy_poisson_kl_rigidity_mu : Measure ℝ
  xi_cauchy_poisson_kl_rigidity_isProbability :
    IsProbabilityMeasure xi_cauchy_poisson_kl_rigidity_mu
  xi_cauchy_poisson_kl_rigidity_sigma : ℝ
  xi_cauchy_poisson_kl_rigidity_p : ℝ → ℝ
  xi_cauchy_poisson_kl_rigidity_q : ℝ → ℝ
  xi_cauchy_poisson_kl_rigidity_Dkl : ℝ → ℝ
  xi_cauchy_poisson_kl_rigidity_integrable :
    Integrable (fun y : ℝ => y ^ 2) xi_cauchy_poisson_kl_rigidity_mu
  xi_cauchy_poisson_kl_rigidity_sigma_eq_variance :
    xi_cauchy_poisson_kl_rigidity_sigma ^ 2 =
      ∫ y, y ^ 2 ∂xi_cauchy_poisson_kl_rigidity_mu
  xi_cauchy_poisson_kl_rigidity_asymptotic :
    Tendsto
      (fun t : ℝ =>
        t ^ 4 * xi_cauchy_poisson_kl_rigidity_Dkl t)
      atTop (𝓝 (xi_cauchy_poisson_kl_rigidity_sigma ^ 4 / 8))
  xi_cauchy_poisson_kl_rigidity_dirac_eq :
    xi_cauchy_poisson_kl_rigidity_mu = Measure.dirac 0 →
      ∀ t > 0,
        xi_cauchy_poisson_kl_rigidity_p t = xi_cauchy_poisson_kl_rigidity_q t
  xi_cauchy_poisson_kl_rigidity_kl_zero :
    (∀ t > 0,
        xi_cauchy_poisson_kl_rigidity_p t = xi_cauchy_poisson_kl_rigidity_q t) →
      ∀ t > 0,
        xi_cauchy_poisson_kl_rigidity_Dkl t = 0

/-- The KL rigidity claim: `o(t^-4)` is equivalent to zero variance, and zero variance is
equivalent to a Dirac mixing law with equal profiles. -/
def xi_cauchy_poisson_kl_rigidity_claim
    (D : xi_cauchy_poisson_kl_rigidity_data) : Prop :=
  (Tendsto
      (fun t : ℝ =>
        t ^ 4 * D.xi_cauchy_poisson_kl_rigidity_Dkl t)
      atTop (𝓝 0) ↔
      D.xi_cauchy_poisson_kl_rigidity_sigma ^ 2 = 0) ∧
    (D.xi_cauchy_poisson_kl_rigidity_sigma ^ 2 = 0 ↔
      D.xi_cauchy_poisson_kl_rigidity_mu = Measure.dirac 0 ∧
        ∀ t > 0,
          D.xi_cauchy_poisson_kl_rigidity_p t =
            D.xi_cauchy_poisson_kl_rigidity_q t)

/-- Paper label: `cor:xi-cauchy-poisson-kl-rigidity`. -/
theorem paper_xi_cauchy_poisson_kl_rigidity
    (D : xi_cauchy_poisson_kl_rigidity_data) :
    xi_cauchy_poisson_kl_rigidity_claim D := by
  letI : IsProbabilityMeasure D.xi_cauchy_poisson_kl_rigidity_mu :=
    D.xi_cauchy_poisson_kl_rigidity_isProbability
  simpa [xi_cauchy_poisson_kl_rigidity_claim] using
    paper_xi_poisson_cauchy_mixture_t4_optimality_rigidity
      D.xi_cauchy_poisson_kl_rigidity_mu
      D.xi_cauchy_poisson_kl_rigidity_sigma
      D.xi_cauchy_poisson_kl_rigidity_p
      D.xi_cauchy_poisson_kl_rigidity_q
      D.xi_cauchy_poisson_kl_rigidity_Dkl
      D.xi_cauchy_poisson_kl_rigidity_integrable
      D.xi_cauchy_poisson_kl_rigidity_sigma_eq_variance
      D.xi_cauchy_poisson_kl_rigidity_asymptotic
      D.xi_cauchy_poisson_kl_rigidity_dirac_eq
      D.xi_cauchy_poisson_kl_rigidity_kl_zero

end

end Omega.Zeta
