import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-fiber data for the uniform fiber lift Renyi maximizer package.

The fields record the finite-fiber moment decomposition and the resulting signed
Renyi-divergence average.  No abstract propositions are quantified over: every
hypothesis is an identity or inequality between the concrete numerical data in this package. -/
structure xi_time_part9g_renyi_maximizer_fiber_uniform_data where
  xi_time_part9g_renyi_maximizer_fiber_uniform_order : ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_order_pos :
    0 < xi_time_part9g_renyi_maximizer_fiber_uniform_order
  xi_time_part9g_renyi_maximizer_fiber_uniform_order_ne_one :
    xi_time_part9g_renyi_maximizer_fiber_uniform_order ≠ 1
  xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_entropy : ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_lift_entropy : ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent : ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_weighted_divergence_average : ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_weighted_divergence_average_pos :
    0 < xi_time_part9g_renyi_maximizer_fiber_uniform_weighted_divergence_average
  xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_decomposition :
    xi_time_part9g_renyi_maximizer_fiber_uniform_lift_entropy =
      xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_entropy -
        xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent
  xi_time_part9g_renyi_maximizer_fiber_uniform_gap_log_identity :
    xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent =
      (1 / (xi_time_part9g_renyi_maximizer_fiber_uniform_order - 1)) *
        Real.log xi_time_part9g_renyi_maximizer_fiber_uniform_weighted_divergence_average
  xi_time_part9g_renyi_maximizer_fiber_uniform_gap_nonneg :
    0 ≤ xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent
  xi_time_part9g_renyi_maximizer_fiber_uniform_base_fiber_moment : ℕ → ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_fiber_moment : ℕ → ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_divergence_fiber_factor : ℕ → ℝ
  xi_time_part9g_renyi_maximizer_fiber_uniform_fiber_moment_identity :
    ∀ x : ℕ,
      xi_time_part9g_renyi_maximizer_fiber_uniform_base_fiber_moment x =
        xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_fiber_moment x *
          xi_time_part9g_renyi_maximizer_fiber_uniform_divergence_fiber_factor x

namespace xi_time_part9g_renyi_maximizer_fiber_uniform_data

/-- The entropy gap between the fiber-uniform lift and an arbitrary lift with the same base law. -/
def xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap
    (D : xi_time_part9g_renyi_maximizer_fiber_uniform_data) : ℝ :=
  D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_entropy -
    D.xi_time_part9g_renyi_maximizer_fiber_uniform_lift_entropy

/-- The uniform-lift maximality assertion for the packaged lift. -/
def xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_maximizes
    (D : xi_time_part9g_renyi_maximizer_fiber_uniform_data) : Prop :=
  D.xi_time_part9g_renyi_maximizer_fiber_uniform_lift_entropy ≤
    D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_entropy

/-- The fiberwise Renyi moment decomposition supplied by the finite-fiber disintegration. -/
def xi_time_part9g_renyi_maximizer_fiber_uniform_fiber_decomposition
    (D : xi_time_part9g_renyi_maximizer_fiber_uniform_data) : Prop :=
  ∀ x : ℕ,
    D.xi_time_part9g_renyi_maximizer_fiber_uniform_base_fiber_moment x =
      D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_fiber_moment x *
        D.xi_time_part9g_renyi_maximizer_fiber_uniform_divergence_fiber_factor x

/-- Paper-facing statement: the finite-fiber decomposition gives the uniform-lift maximality and
the displayed logarithmic Renyi-divergence entropy-gap formula. -/
def xi_time_part9g_renyi_maximizer_fiber_uniform_statement
    (D : xi_time_part9g_renyi_maximizer_fiber_uniform_data) : Prop :=
  D.xi_time_part9g_renyi_maximizer_fiber_uniform_fiber_decomposition ∧
    D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_maximizes ∧
      D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap =
        D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent ∧
        D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap =
          (1 / (D.xi_time_part9g_renyi_maximizer_fiber_uniform_order - 1)) *
            Real.log
              D.xi_time_part9g_renyi_maximizer_fiber_uniform_weighted_divergence_average

end xi_time_part9g_renyi_maximizer_fiber_uniform_data

open xi_time_part9g_renyi_maximizer_fiber_uniform_data

/-- Paper label: `thm:xi-time-part9g-renyi-maximizer-fiber-uniform`. -/
theorem paper_xi_time_part9g_renyi_maximizer_fiber_uniform
    (D : xi_time_part9g_renyi_maximizer_fiber_uniform_data) :
    xi_time_part9g_renyi_maximizer_fiber_uniform_statement D := by
  have hgap :
      D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap =
        D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent := by
    dsimp [xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap]
    rw [D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_decomposition]
    ring
  have hmax :
      D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_maximizes := by
    dsimp [xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_maximizes]
    have hgap_eq' :
        D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_entropy -
            D.xi_time_part9g_renyi_maximizer_fiber_uniform_lift_entropy =
          D.xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap_exponent := by
      simpa [xi_time_part9g_renyi_maximizer_fiber_uniform_entropy_gap] using hgap
    have hgap_nonneg :
        0 ≤
          D.xi_time_part9g_renyi_maximizer_fiber_uniform_uniform_entropy -
            D.xi_time_part9g_renyi_maximizer_fiber_uniform_lift_entropy := by
      rw [hgap_eq']
      exact D.xi_time_part9g_renyi_maximizer_fiber_uniform_gap_nonneg
    exact sub_nonneg.mp hgap_nonneg
  refine ⟨D.xi_time_part9g_renyi_maximizer_fiber_uniform_fiber_moment_identity, hmax,
    hgap, ?_⟩
  rw [hgap, D.xi_time_part9g_renyi_maximizer_fiber_uniform_gap_log_identity]

end

end Omega.Zeta
