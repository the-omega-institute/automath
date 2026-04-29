import Mathlib

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The common endpoint scale used after extracting the minimal exponent. -/
def xi_statewise_endpoint_dimension_lower_envelope_scale (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹

/-- A finite positive mixture of statewise endpoint probes. -/
def xi_statewise_endpoint_dimension_lower_envelope_mixture {m : ℕ}
    (t : Fin m → ℝ) (x : Fin m → ℕ → ℝ) (N : ℕ) : ℝ :=
  Finset.univ.sum fun i : Fin m => t i * x i N

/-- The upper envelope constant obtained by summing component upper constants. -/
def xi_statewise_endpoint_dimension_lower_envelope_upperConstant {m : ℕ}
    (t C : Fin m → ℝ) : ℝ :=
  Finset.univ.sum fun i : Fin m => t i * C i

/-- Paper-facing lower-envelope statement for finite positive convex combinations. -/
def xi_statewise_endpoint_dimension_lower_envelope_statement : Prop :=
  ∀ {m : ℕ} (i₀ : Fin m) (t C : Fin m → ℝ) (x : Fin m → ℕ → ℝ)
      (c₀ : ℝ) (N₀ : ℕ),
    0 < c₀ →
      (∀ i, 0 ≤ t i) →
      (∀ i, 0 ≤ C i) →
      (∀ i N, N₀ ≤ N → 0 ≤ x i N) →
      (∀ N, N₀ ≤ N →
        c₀ * xi_statewise_endpoint_dimension_lower_envelope_scale N ≤ x i₀ N) →
      (∀ i N, N₀ ≤ N →
        x i N ≤ C i * xi_statewise_endpoint_dimension_lower_envelope_scale N) →
      ∀ N, N₀ ≤ N →
        t i₀ * c₀ * xi_statewise_endpoint_dimension_lower_envelope_scale N ≤
            xi_statewise_endpoint_dimension_lower_envelope_mixture t x N ∧
          xi_statewise_endpoint_dimension_lower_envelope_mixture t x N ≤
            xi_statewise_endpoint_dimension_lower_envelope_upperConstant t C *
              xi_statewise_endpoint_dimension_lower_envelope_scale N

/-- Paper label: `prop:xi-statewise-endpoint-dimension-lower-envelope`. -/
theorem paper_xi_statewise_endpoint_dimension_lower_envelope :
    xi_statewise_endpoint_dimension_lower_envelope_statement := by
  intro m i₀ t C x c₀ N₀ hc₀ ht hC hx_nonneg hx_lower hx_upper N hN
  constructor
  · have hterm_nonneg :
        ∀ i : Fin m, i ∈ (Finset.univ : Finset (Fin m)) → 0 ≤ t i * x i N := by
      intro i _hi
      exact mul_nonneg (ht i) (hx_nonneg i N hN)
    have hsingle :
        t i₀ * x i₀ N ≤
          Finset.univ.sum fun i : Fin m => t i * x i N :=
      Finset.single_le_sum hterm_nonneg (Finset.mem_univ i₀)
    have hminimal :
        t i₀ * c₀ * xi_statewise_endpoint_dimension_lower_envelope_scale N ≤
          t i₀ * x i₀ N := by
      calc
        t i₀ * c₀ * xi_statewise_endpoint_dimension_lower_envelope_scale N =
            t i₀ * (c₀ * xi_statewise_endpoint_dimension_lower_envelope_scale N) := by ring
        _ ≤ t i₀ * x i₀ N := mul_le_mul_of_nonneg_left (hx_lower N hN) (ht i₀)
    exact le_trans hminimal hsingle
  · unfold xi_statewise_endpoint_dimension_lower_envelope_mixture
      xi_statewise_endpoint_dimension_lower_envelope_upperConstant
    calc
      (Finset.univ.sum fun i : Fin m => t i * x i N) ≤
          Finset.univ.sum fun i : Fin m =>
            t i * (C i * xi_statewise_endpoint_dimension_lower_envelope_scale N) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        exact mul_le_mul_of_nonneg_left (hx_upper i N hN) (ht i)
      _ =
          (Finset.univ.sum fun i : Fin m => t i * C i) *
            xi_statewise_endpoint_dimension_lower_envelope_scale N := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring

end

end Omega.Zeta
