import Omega.Zeta.CauchyPoissonSixthSignatureNegativityRigidity

namespace Omega.Zeta

noncomputable section

/-- Closed fourth-order KL coefficient reused by termwise differentiation. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT4 (sigmaSq : ℝ) : ℝ :=
  sigmaSq ^ 2 / 8

/-- Closed sixth-order KL coefficient reused by termwise differentiation. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT6
    (sigmaSq mu3 mu4 : ℝ) : ℝ :=
  3 * mu3 ^ 2 / 32 - sigmaSq * mu4 / 8 + sigmaSq ^ 3 / 64

/-- The `t^{-5}` Fisher coefficient obtained by differentiating the `t^{-4}` KL term. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_t5Coeff (sigmaSq : ℝ) : ℝ :=
  4 * xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT4 sigmaSq

/-- Closed form of the `t^{-5}` Fisher coefficient. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_closed_t5 (sigmaSq : ℝ) : ℝ :=
  sigmaSq ^ 2 / 2

/-- The `t^{-7}` Fisher coefficient obtained by differentiating the `t^{-6}` KL term. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_t7Coeff
    (sigma mu3 mu4 : ℝ) : ℝ :=
  6 * xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT6 (sigma ^ 2) mu3 mu4

/-- Closed sixth-order Fisher coefficient in the displayed paper normalization. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_closed_t7
    (sigma mu3 mu4 : ℝ) : ℝ :=
  (3 / 32 : ℝ) * (sigma ^ 6 - 8 * sigma ^ 2 * mu4 + 6 * mu3 ^ 2)

/-- Concrete formal statement for `cor:xi-cauchy-poisson-fisher-sharp-asymptotics`. -/
def xi_cauchy_poisson_fisher_sharp_asymptotics_statement : Prop :=
  (∀ sigmaSq : ℝ,
    xi_cauchy_poisson_fisher_sharp_asymptotics_t5Coeff sigmaSq =
      xi_cauchy_poisson_fisher_sharp_asymptotics_closed_t5 sigmaSq) ∧
  (∀ sigma mu3 mu4 : ℝ,
    xi_cauchy_poisson_fisher_sharp_asymptotics_t7Coeff sigma mu3 mu4 =
      xi_cauchy_poisson_fisher_sharp_asymptotics_closed_t7 sigma mu3 mu4) ∧
  ∀ (sigma mu3 mu4 : ℝ), 0 < sigma →
    sigma ^ 2 * mu4 - mu3 ^ 2 - sigma ^ 6 ≥ 0 →
      xi_cauchy_poisson_fisher_sharp_asymptotics_t7Coeff sigma mu3 mu4 ≤
        -(21 * sigma ^ 6) / 32

/-- Paper label: `cor:xi-cauchy-poisson-fisher-sharp-asymptotics`. -/
theorem paper_xi_cauchy_poisson_fisher_sharp_asymptotics :
    xi_cauchy_poisson_fisher_sharp_asymptotics_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro sigmaSq
    simp [xi_cauchy_poisson_fisher_sharp_asymptotics_t5Coeff,
      xi_cauchy_poisson_fisher_sharp_asymptotics_closed_t5,
      xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT4]
    ring
  · intro sigma mu3 mu4
    simp [xi_cauchy_poisson_fisher_sharp_asymptotics_t7Coeff,
      xi_cauchy_poisson_fisher_sharp_asymptotics_closed_t7,
      xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT6]
    ring
  · intro sigma mu3 mu4 hsigma hgram
    have hneg :=
      (paper_xi_cauchy_poisson_sixth_signature_negativity_rigidity sigma mu3 mu4
        hsigma hgram).2.1
    have hcoeff :
        xi_cauchy_poisson_fisher_sharp_asymptotics_t7Coeff sigma mu3 mu4 =
          6 * (sigma ^ 6 *
            (1 - 8 * (mu4 / sigma ^ 4) + 6 * (mu3 / sigma ^ 3) ^ 2) / 64) := by
      simp [xi_cauchy_poisson_fisher_sharp_asymptotics_t7Coeff,
        xi_cauchy_poisson_fisher_sharp_asymptotics_klClosedT6]
      field_simp [ne_of_gt hsigma]
      ring
    rw [hcoeff]
    nlinarith [hneg, sq_nonneg mu3]

end

end Omega.Zeta
