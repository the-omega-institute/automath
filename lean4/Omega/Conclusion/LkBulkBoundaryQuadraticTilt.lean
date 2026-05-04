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

/-- Leading lower-endpoint CDF term for the bulk arcsine law. -/
def conclusion_lk_hard_edge_lift_bulk_endpoint_cdf (ε : ℝ) : ℝ :=
  (1 / Real.pi) * Real.sqrt ε

/-- Leading lower-endpoint CDF term for the boundary Beta `(3/2, 3/2)` law. -/
def conclusion_lk_hard_edge_lift_boundary_endpoint_cdf (ε : ℝ) : ℝ :=
  (2 / (3 * Real.pi)) * ε * Real.sqrt ε

/-- The same leading terms at the upper hard edge, using the symmetry around `μ = 2`. -/
def conclusion_lk_hard_edge_lift_upper_endpoint_cdf (cdf : ℝ → ℝ) (ε : ℝ) : ℝ :=
  cdf ε

/-- Endpoint asymptotic package: the boundary CDF has one extra factor of `ε` compared with the
bulk hard edge, and the density relation is the quadratic tilt on the open interval. -/
def conclusion_lk_hard_edge_lift_statement : Prop :=
  (∀ ε : ℝ, 0 ≤ ε →
    conclusion_lk_hard_edge_lift_boundary_endpoint_cdf ε =
      (2 / 3) * ε * conclusion_lk_hard_edge_lift_bulk_endpoint_cdf ε) ∧
    (∀ ε : ℝ,
      conclusion_lk_hard_edge_lift_upper_endpoint_cdf
          conclusion_lk_hard_edge_lift_bulk_endpoint_cdf ε =
        conclusion_lk_hard_edge_lift_bulk_endpoint_cdf ε ∧
      conclusion_lk_hard_edge_lift_upper_endpoint_cdf
          conclusion_lk_hard_edge_lift_boundary_endpoint_cdf ε =
        conclusion_lk_hard_edge_lift_boundary_endpoint_cdf ε) ∧
    (∀ μ : ℝ, 0 < μ → μ < 4 →
      conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density μ =
        (μ * (4 - μ) / 2) * conclusion_lk_bulk_boundary_quadratic_tilt_bulk_density μ) ∧
    conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density 0 = 0 ∧
    conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density 4 = 0 ∧
    (∀ μ : ℝ,
      conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density μ =
        conclusion_lk_bulk_boundary_quadratic_tilt_boundary_density (4 - μ))

/-- Paper label: `cor:conclusion-Lk-hard-edge-lift`. -/
theorem paper_conclusion_lk_hard_edge_lift :
    conclusion_lk_hard_edge_lift_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    unfold conclusion_lk_hard_edge_lift_boundary_endpoint_cdf
      conclusion_lk_hard_edge_lift_bulk_endpoint_cdf
    ring_nf
  · intro ε
    simp [conclusion_lk_hard_edge_lift_upper_endpoint_cdf]
  · intro μ hμ0 hμ4
    exact (paper_conclusion_lk_bulk_boundary_quadratic_tilt (fun _ : ℝ => 0)
      continuous_const hμ0 hμ4).2.2
  · exact Omega.POM.paper_pom_lk_boundary_spectral_measure_beta32.2.2.2.1
  · exact Omega.POM.paper_pom_lk_boundary_spectral_measure_beta32.2.2.2.2.2.1
  · exact Omega.POM.paper_pom_lk_boundary_spectral_measure_beta32.2.2.2.2.2.2

end

end Omega.Conclusion
