import Mathlib.Tactic
import Omega.Zeta.CauchyPoissonKlGoldenScale

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-cauchy-poisson-entropy-curvature-invariant`. -/
theorem paper_xi_cauchy_poisson_entropy_curvature_invariant
    (D : xi_cauchy_poisson_kl_golden_scale_data) :
    D.correctionCoefficient =
        3 * D.xi_cauchy_poisson_kl_golden_scale_mu3 ^ 2 / 32 -
          D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 2 *
            D.xi_cauchy_poisson_kl_golden_scale_mu4 / 8 +
            D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 6 / 64 ∧
      (D.xi_cauchy_poisson_kl_golden_scale_mu3 = 0 →
        D.correctionCoefficient =
          D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 6 / 64 -
            D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 2 *
              D.xi_cauchy_poisson_kl_golden_scale_mu4 / 8) := by
  refine ⟨rfl, ?_⟩
  intro hmu3
  rw [xi_cauchy_poisson_kl_golden_scale_data.correctionCoefficient, hmu3]
  ring

end

end Omega.Zeta
