import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Alternating endpoint finite-window sum. -/
def xi_busemann_depth_finite_window_estimator_endpoint_sum (N : ℕ) (a : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), (-a) ^ k

/-- Norm-squared finite-window sum for the same endpoint ratio. -/
def xi_busemann_depth_finite_window_estimator_norm_sq_sum (N : ℕ) (a : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), Complex.normSq ((-a) ^ k)

/-- Geometric closed form for the norm-squared finite-window terms. -/
def xi_busemann_depth_finite_window_estimator_norm_sq_geometric_sum
    (N : ℕ) (a : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), Complex.normSq a ^ k

/-- The finite-window depth statement: endpoint closed form, norm-squared closed form, and the
disk-hypothesis exponential error bound. -/
def xi_busemann_depth_finite_window_estimator_statement (N : ℕ) (a : ℂ) : Prop :=
  (1 + a) * xi_busemann_depth_finite_window_estimator_endpoint_sum N a =
      1 - (-a) ^ (N + 1) ∧
    xi_busemann_depth_finite_window_estimator_norm_sq_sum N a =
      xi_busemann_depth_finite_window_estimator_norm_sq_geometric_sum N a ∧
    (1 - Complex.normSq a) *
        xi_busemann_depth_finite_window_estimator_norm_sq_sum N a =
      1 - Complex.normSq a ^ (N + 1) ∧
    ∀ r : ℝ, ‖a‖ ≤ r → r < 1 →
      ‖(1 + a) * xi_busemann_depth_finite_window_estimator_endpoint_sum N a - 1‖ ≤
        r ^ (N + 1)

lemma xi_busemann_depth_finite_window_estimator_normSq_pow (z : ℂ) (k : ℕ) :
    Complex.normSq (z ^ k) = Complex.normSq z ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

/-- Paper label: `thm:xi-busemann-depth-finite-window-estimator`. -/
theorem paper_xi_busemann_depth_finite_window_estimator (N : ℕ) (a : ℂ) :
    xi_busemann_depth_finite_window_estimator_statement N a := by
  have hEndpoint :
      (1 + a) * xi_busemann_depth_finite_window_estimator_endpoint_sum N a =
        1 - (-a) ^ (N + 1) := by
    have h := mul_neg_geom_sum (-a) (N + 1)
    simpa [xi_busemann_depth_finite_window_estimator_endpoint_sum, sub_neg_eq_add] using h
  have hNormSq :
      xi_busemann_depth_finite_window_estimator_norm_sq_sum N a =
        xi_busemann_depth_finite_window_estimator_norm_sq_geometric_sum N a := by
    unfold xi_busemann_depth_finite_window_estimator_norm_sq_sum
      xi_busemann_depth_finite_window_estimator_norm_sq_geometric_sum
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [xi_busemann_depth_finite_window_estimator_normSq_pow, Complex.normSq_neg]
  have hNormClosed :
      (1 - Complex.normSq a) *
          xi_busemann_depth_finite_window_estimator_norm_sq_sum N a =
        1 - Complex.normSq a ^ (N + 1) := by
    rw [hNormSq]
    have h := mul_neg_geom_sum (Complex.normSq a) (N + 1)
    simpa [xi_busemann_depth_finite_window_estimator_norm_sq_geometric_sum] using h
  refine ⟨hEndpoint, hNormSq, hNormClosed, ?_⟩
  intro r hr _hr_lt
  have hpow_le : ‖a‖ ^ (N + 1) ≤ r ^ (N + 1) :=
    pow_le_pow_left₀ (norm_nonneg a) hr (N + 1)
  calc
    ‖(1 + a) * xi_busemann_depth_finite_window_estimator_endpoint_sum N a - 1‖
        = ‖(-a) ^ (N + 1)‖ := by
          rw [hEndpoint]
          simp
    _ = ‖a‖ ^ (N + 1) := by
          simp [norm_pow]
    _ ≤ r ^ (N + 1) := hpow_le

end

end Omega.Zeta
