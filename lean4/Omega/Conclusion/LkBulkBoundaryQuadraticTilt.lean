import Mathlib.Tactic
import Omega.POM.LkArcsineLaw
import Omega.POM.LkBoundaryBulkRadonNikodym
import Omega.POM.LkBoundarySpectralMeasureBeta32

open Filter Topology

namespace Omega.Conclusion

noncomputable section

/-- Bulk arcsine density on `(0, 4)` used in the conclusion-level wrapper. -/
def conclusion_lk_bulk_boundary_quadratic_tilt_bulk_density (μ : ℝ) : ℝ :=
  1 / (Real.pi * Real.sqrt (μ * (4 - μ)))

/-- Boundary Beta `(3/2, 3/2)` density on `(0, 4)` used in the conclusion-level wrapper. -/
def conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density (μ : ℝ) : ℝ :=
  Omega.POM.pom_lk_boundary_spectral_measure_beta32_density μ

/-- Boundary Beta `(3/2, 3/2)` package used in the conclusion-level wrapper. -/
def conclusion_lk_bulk_boundary_quadratic_tilt_boundary_beta_statement : Prop :=
  (∀ k : ℕ, ∀ p : Fin k,
      Omega.POM.pom_lk_boundary_spectral_measure_beta32_weight k p =
        (4 : ℝ) / (2 * k + 1) *
          Real.sin (Omega.POM.pom_lk_boundary_spectral_measure_beta32_angle k p) ^ 2) ∧
    (∑ p : Fin 1, Omega.POM.pom_lk_boundary_spectral_measure_beta32_weight 1 p = 1) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi →
      let μ := Omega.POM.pom_lk_boundary_spectral_measure_beta32_mu θ
      μ * (4 - μ) = 4 * Real.sin θ ^ 2 ∧
        Omega.POM.pom_lk_boundary_spectral_measure_beta32_density μ = Real.sin θ / Real.pi) ∧
    Omega.POM.pom_lk_boundary_spectral_measure_beta32_density 0 = 0 ∧
    Omega.POM.pom_lk_boundary_spectral_measure_beta32_density 2 = 1 / Real.pi ∧
    Omega.POM.pom_lk_boundary_spectral_measure_beta32_density 4 = 0 ∧
    (∀ μ : ℝ,
      Omega.POM.pom_lk_boundary_spectral_measure_beta32_density μ =
        Omega.POM.pom_lk_boundary_spectral_measure_beta32_density (4 - μ))

/-- Paper label: `thm:conclusion-Lk-bulk-boundary-quadratic-tilt`. The bulk arcsine limit, the
boundary Beta `(3/2, 3/2)` package, and the bulk-to-boundary Radon--Nikodym identity are
collected into one conclusion-level quadratic-tilt wrapper. -/
theorem paper_conclusion_lk_bulk_boundary_quadratic_tilt
    (f : ℝ → ℝ) (hf : Continuous f) {μ : ℝ} (hμ0 : 0 < μ) (hμ4 : μ < 4) :
    Tendsto (fun k : ℕ => Omega.POM.lkEmpiricalAverage k f) atTop
      (𝓝 (Omega.POM.arcsineAverage f)) ∧
      conclusion_lk_bulk_boundary_quadratic_tilt_boundary_beta_statement ∧
      conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density μ =
        (μ * (4 - μ) / 2) * conclusion_lk_bulk_boundary_quadratic_tilt_bulk_density μ := by
  refine ⟨Omega.POM.paper_pom_Lk_arcsine_law f hf, ?_, ?_⟩
  · exact Omega.POM.paper_pom_lk_boundary_spectral_measure_beta32
  · unfold conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density
      conclusion_lk_bulk_boundary_quadratic_tilt_bulk_density
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Omega.POM.paper_pom_lk_boundary_bulk_radon_nikodym hμ0 hμ4

end

end Omega.Conclusion
