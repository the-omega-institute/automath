import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete finite spectral package for the tau hitting-time tail. The dominant root controls
the exponential tail, and the analytic radius is recorded as the reciprocal spectral radius. -/
structure pom_tau_exponential_tail_analytic_disk_data where
  pom_tau_exponential_tail_analytic_disk_tail : ℕ → ℝ
  pom_tau_exponential_tail_analytic_disk_prefactor : ℝ
  pom_tau_exponential_tail_analytic_disk_dominantEigenvalue : ℝ
  pom_tau_exponential_tail_analytic_disk_spectralRadius : ℝ
  pom_tau_exponential_tail_analytic_disk_analyticDiskRadius : ℝ
  pom_tau_exponential_tail_analytic_disk_dominant_pos :
    0 < pom_tau_exponential_tail_analytic_disk_dominantEigenvalue
  pom_tau_exponential_tail_analytic_disk_tail_bound :
    ∀ n,
      |pom_tau_exponential_tail_analytic_disk_tail n| ≤
        pom_tau_exponential_tail_analytic_disk_prefactor *
          pom_tau_exponential_tail_analytic_disk_dominantEigenvalue ^ n
  pom_tau_exponential_tail_analytic_disk_spectralRadius_eq :
    pom_tau_exponential_tail_analytic_disk_spectralRadius =
      pom_tau_exponential_tail_analytic_disk_dominantEigenvalue
  pom_tau_exponential_tail_analytic_disk_analyticDiskRadius_eq :
    pom_tau_exponential_tail_analytic_disk_analyticDiskRadius =
      pom_tau_exponential_tail_analytic_disk_spectralRadius⁻¹

namespace pom_tau_exponential_tail_analytic_disk_data

/-- The dominant-eigenvalue package gives a uniform exponential tail envelope. -/
def exponentialTailBounds (D : pom_tau_exponential_tail_analytic_disk_data) : Prop :=
  ∀ n,
    |D.pom_tau_exponential_tail_analytic_disk_tail n| ≤
      D.pom_tau_exponential_tail_analytic_disk_prefactor *
        D.pom_tau_exponential_tail_analytic_disk_dominantEigenvalue ^ n

/-- The maximal analytic disk radius is the reciprocal of the spectral radius. -/
def maximalAnalyticDisk (D : pom_tau_exponential_tail_analytic_disk_data) : Prop :=
  D.pom_tau_exponential_tail_analytic_disk_analyticDiskRadius =
      D.pom_tau_exponential_tail_analytic_disk_dominantEigenvalue⁻¹ ∧
    0 < D.pom_tau_exponential_tail_analytic_disk_analyticDiskRadius

end pom_tau_exponential_tail_analytic_disk_data

open pom_tau_exponential_tail_analytic_disk_data

/-- Paper label: `prop:pom-tau-exponential-tail-analytic-disk`. -/
theorem paper_pom_tau_exponential_tail_analytic_disk
    (D : pom_tau_exponential_tail_analytic_disk_data) :
    D.exponentialTailBounds ∧ D.maximalAnalyticDisk := by
  refine ⟨D.pom_tau_exponential_tail_analytic_disk_tail_bound, ?_⟩
  constructor
  · calc
      D.pom_tau_exponential_tail_analytic_disk_analyticDiskRadius
          = D.pom_tau_exponential_tail_analytic_disk_spectralRadius⁻¹ :=
            D.pom_tau_exponential_tail_analytic_disk_analyticDiskRadius_eq
      _ = D.pom_tau_exponential_tail_analytic_disk_dominantEigenvalue⁻¹ := by
        rw [D.pom_tau_exponential_tail_analytic_disk_spectralRadius_eq]
  · rw [D.pom_tau_exponential_tail_analytic_disk_analyticDiskRadius_eq,
      D.pom_tau_exponential_tail_analytic_disk_spectralRadius_eq]
    exact inv_pos.mpr D.pom_tau_exponential_tail_analytic_disk_dominant_pos

end
end Omega.POM
