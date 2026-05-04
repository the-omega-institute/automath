import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The affine tangent model used for adjacent cumulant growth. -/
noncomputable def xi_terminal_zm_cumulant_local_growth_dense_affine_tan_model
    (phase : ℕ → ℝ) (slope intercept : ℝ) (error : ℕ → ℝ) (n : ℕ) : ℝ :=
  slope * Real.tan (phase n) + intercept + error n

/-- Concrete adjacent-growth data for the terminal `zm` cumulants.  The ratio is recorded as an
affine transform of `tan (phase n)` plus a residual error; the dense and unbounded cluster fields
are stated for that affine tangent model and transported to the actual ratio by the theorem. -/
structure xi_terminal_zm_cumulant_local_growth_dense_data where
  xi_terminal_zm_cumulant_local_growth_dense_ratio : ℕ → ℝ
  xi_terminal_zm_cumulant_local_growth_dense_phase : ℕ → ℝ
  xi_terminal_zm_cumulant_local_growth_dense_slope : ℝ
  xi_terminal_zm_cumulant_local_growth_dense_intercept : ℝ
  xi_terminal_zm_cumulant_local_growth_dense_error : ℕ → ℝ
  xi_terminal_zm_cumulant_local_growth_dense_ratio_affine_tan :
    ∀ n : ℕ,
      xi_terminal_zm_cumulant_local_growth_dense_ratio n =
        xi_terminal_zm_cumulant_local_growth_dense_affine_tan_model
          xi_terminal_zm_cumulant_local_growth_dense_phase
          xi_terminal_zm_cumulant_local_growth_dense_slope
          xi_terminal_zm_cumulant_local_growth_dense_intercept
          xi_terminal_zm_cumulant_local_growth_dense_error n
  xi_terminal_zm_cumulant_local_growth_dense_affine_tan_cluster_dense :
    ∀ target epsilon : ℝ, 0 < epsilon →
      ∃ n : ℕ,
        |xi_terminal_zm_cumulant_local_growth_dense_affine_tan_model
            xi_terminal_zm_cumulant_local_growth_dense_phase
            xi_terminal_zm_cumulant_local_growth_dense_slope
            xi_terminal_zm_cumulant_local_growth_dense_intercept
            xi_terminal_zm_cumulant_local_growth_dense_error n -
          target| < epsilon
  xi_terminal_zm_cumulant_local_growth_dense_affine_tan_cluster_at_infinity :
    ∀ bound : ℝ, ∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
          bound <
            |xi_terminal_zm_cumulant_local_growth_dense_affine_tan_model
              xi_terminal_zm_cumulant_local_growth_dense_phase
              xi_terminal_zm_cumulant_local_growth_dense_slope
              xi_terminal_zm_cumulant_local_growth_dense_intercept
              xi_terminal_zm_cumulant_local_growth_dense_error n|

namespace xi_terminal_zm_cumulant_local_growth_dense_data

/-- The real cluster set of the adjacent-growth ratio is dense. -/
def xi_terminal_zm_cumulant_local_growth_dense_real_cluster_dense
    (D : xi_terminal_zm_cumulant_local_growth_dense_data) : Prop :=
  ∀ target epsilon : ℝ, 0 < epsilon →
    ∃ n : ℕ,
      |D.xi_terminal_zm_cumulant_local_growth_dense_ratio n - target| < epsilon

/-- The adjacent-growth ratio has arbitrarily late excursions beyond any finite bound. -/
def xi_terminal_zm_cumulant_local_growth_dense_infinite_cluster_at_infinity
    (D : xi_terminal_zm_cumulant_local_growth_dense_data) : Prop :=
  ∀ bound : ℝ, ∀ N : ℕ,
    ∃ n : ℕ,
      N ≤ n ∧ bound < |D.xi_terminal_zm_cumulant_local_growth_dense_ratio n|

end xi_terminal_zm_cumulant_local_growth_dense_data

/-- Paper label: `prop:xi-terminal-zm-cumulant-local-growth-dense`. -/
theorem paper_xi_terminal_zm_cumulant_local_growth_dense
    (D : xi_terminal_zm_cumulant_local_growth_dense_data) :
    D.xi_terminal_zm_cumulant_local_growth_dense_real_cluster_dense ∧
      D.xi_terminal_zm_cumulant_local_growth_dense_infinite_cluster_at_infinity := by
  constructor
  · intro target epsilon hepsilon
    rcases D.xi_terminal_zm_cumulant_local_growth_dense_affine_tan_cluster_dense target epsilon
        hepsilon with
      ⟨n, hn⟩
    exact ⟨n, by simpa [D.xi_terminal_zm_cumulant_local_growth_dense_ratio_affine_tan n] using hn⟩
  · intro bound N
    rcases D.xi_terminal_zm_cumulant_local_growth_dense_affine_tan_cluster_at_infinity bound
        N with
      ⟨n, hnN, hn_bound⟩
    exact
      ⟨n, hnN,
        by
          simpa [D.xi_terminal_zm_cumulant_local_growth_dense_ratio_affine_tan n] using hn_bound⟩

end Omega.Zeta
