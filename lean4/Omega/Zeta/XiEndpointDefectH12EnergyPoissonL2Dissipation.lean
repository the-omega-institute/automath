import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Total mass of the finite endpoint-defect profile. -/
def xiEndpointTotalMass {κ : ℕ} (mass : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j

/-- Weighted defect amplitude `Σ_j m_j δ_j`. -/
def xiEndpointWeightedDefect {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * δ j

/-- Finite averaged Poisson profile on the near side. -/
noncomputable def xiEndpointPt {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  (∑ j, mass j * (1 - δ j)) / xiEndpointTotalMass mass

/-- Finite averaged Poisson profile on the far side. -/
noncomputable def xiEndpointQt {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  (∑ j, mass j * (1 + δ j)) / xiEndpointTotalMass mass

/-- The normalized Poisson gap `p_t - q_t` in the finite endpoint model. -/
noncomputable def xiEndpointPoissonGap {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  (-2) * xiEndpointWeightedDefect mass δ / xiEndpointTotalMass mass

/-- The finite `L²` dissipation proxy associated to the Poisson gap. -/
noncomputable def xiEndpointPoissonL2Dissipation {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  (xiEndpointPoissonGap mass δ) ^ 2

/-- The corresponding `Ḣ^{1/2}` energy proxy. -/
noncomputable def xiEndpointH12Energy {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  (2 * Real.pi * xiEndpointWeightedDefect mass δ / xiEndpointTotalMass mass) ^ 2

private theorem xiEndpoint_pt_sub_qt {κ : ℕ} (mass δ : Fin κ → ℝ)
    (hM : xiEndpointTotalMass mass ≠ 0) :
    xiEndpointPt mass δ - xiEndpointQt mass δ = xiEndpointPoissonGap mass δ := by
  have hpt :
      ∑ j, mass j * (1 - δ j) =
        (∑ j, mass j) - ∑ j, mass j * δ j := by
    calc
      ∑ j, mass j * (1 - δ j) = ∑ j, (mass j - mass j * δ j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = (∑ j, mass j) - ∑ j, mass j * δ j := by
        rw [Finset.sum_sub_distrib]
  have hqt :
      ∑ j, mass j * (1 + δ j) =
        (∑ j, mass j) + ∑ j, mass j * δ j := by
    calc
      ∑ j, mass j * (1 + δ j) = ∑ j, (mass j + mass j * δ j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = (∑ j, mass j) + ∑ j, mass j * δ j := by
        rw [Finset.sum_add_distrib]
  unfold xiEndpointPt xiEndpointQt xiEndpointPoissonGap xiEndpointWeightedDefect xiEndpointTotalMass
  rw [hpt, hqt]
  field_simp [hM]
  ring

private theorem xiEndpoint_energy_eq_pi_sq_dissipation {κ : ℕ} (mass δ : Fin κ → ℝ)
    (hM : xiEndpointTotalMass mass ≠ 0) :
    xiEndpointH12Energy mass δ = Real.pi ^ 2 * xiEndpointPoissonL2Dissipation mass δ := by
  unfold xiEndpointH12Energy xiEndpointPoissonL2Dissipation xiEndpointPoissonGap
  field_simp [hM]

/-- Finite endpoint-defect energy identity: the `Ḣ^{1/2}` energy is the square of the Poisson
gap up to the universal `π²` factor, and the normalized near/far Poisson profiles differ by the
expected two-scale defect amplitude.
    thm:xi-endpoint-defect-h12-energy-poisson-l2-dissipation -/
theorem paper_xi_endpoint_defect_h12_energy_poisson_l2_dissipation :
    ∀ {κ : ℕ} (mass δ : Fin κ → ℝ), xiEndpointTotalMass mass ≠ 0 →
      xiEndpointPt mass δ - xiEndpointQt mass δ = xiEndpointPoissonGap mass δ ∧
        xiEndpointH12Energy mass δ =
          Real.pi ^ 2 * xiEndpointPoissonL2Dissipation mass δ ∧
        0 ≤ xiEndpointH12Energy mass δ := by
  intro κ mass δ hM
  have hnonneg : 0 ≤ xiEndpointH12Energy mass δ := by
    unfold xiEndpointH12Energy
    positivity
  exact ⟨xiEndpoint_pt_sub_qt mass δ hM, xiEndpoint_energy_eq_pi_sq_dissipation mass δ hM, hnonneg⟩

end Omega.Zeta
