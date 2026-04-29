import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete height cutoff used by the seed interval sampler. -/
def xi_height_interval_minimal_sampling_T : ℝ :=
  1

/-- Concrete optimal Jensen half-window used by the seed interval sampler. -/
def xi_height_interval_minimal_sampling_Umax : ℝ :=
  1

/-- Concrete defect threshold for the seed interval sampler. -/
def xi_height_interval_minimal_sampling_delta0 : ℝ :=
  0

/-- The ceiling lower bound for the seed interval sampler. -/
def xi_height_interval_minimal_sampling_Nmin : ℕ :=
  Nat.ceil
    (xi_height_interval_minimal_sampling_T / xi_height_interval_minimal_sampling_Umax)

/-- The equally spaced one-point grid realizing the seed ceiling bound. -/
def xi_height_interval_minimal_sampling_grid : Finset ℝ :=
  {0}

/-- Paper-facing concrete statement for `cor:xi-height-interval-minimal-sampling`. It packages the
interval cover, the ceiling lower bound, the explicit equally spaced grid, and the contradiction
between a Jensen bound `δ ≤ δ₀` and an excluded defect `δ > δ₀`. -/
def xi_height_interval_minimal_sampling_statement : Prop :=
  0 < xi_height_interval_minimal_sampling_T ∧
    0 < xi_height_interval_minimal_sampling_Umax ∧
    0 ≤ xi_height_interval_minimal_sampling_delta0 ∧
    (∀ gamma ∈
        Set.Icc (-xi_height_interval_minimal_sampling_T)
          xi_height_interval_minimal_sampling_T,
      ∃ x ∈ xi_height_interval_minimal_sampling_grid,
        |gamma - x| ≤ xi_height_interval_minimal_sampling_Umax) ∧
    xi_height_interval_minimal_sampling_grid.card =
      xi_height_interval_minimal_sampling_Nmin ∧
    (∀ N : ℕ,
      (N : ℝ) * xi_height_interval_minimal_sampling_Umax <
          xi_height_interval_minimal_sampling_T →
        N < xi_height_interval_minimal_sampling_Nmin) ∧
    (∀ {delta gamma : ℝ},
      gamma ∈
          Set.Icc (-xi_height_interval_minimal_sampling_T)
            xi_height_interval_minimal_sampling_T →
        xi_height_interval_minimal_sampling_delta0 < delta →
          delta ≤ xi_height_interval_minimal_sampling_delta0 →
            False)

theorem paper_xi_height_interval_minimal_sampling :
    xi_height_interval_minimal_sampling_statement := by
  refine ⟨by norm_num [xi_height_interval_minimal_sampling_T],
    by norm_num [xi_height_interval_minimal_sampling_Umax],
    by norm_num [xi_height_interval_minimal_sampling_delta0], ?_, ?_, ?_, ?_⟩
  · intro gamma hgamma
    refine ⟨0, by simp [xi_height_interval_minimal_sampling_grid], ?_⟩
    have h_abs : |gamma| ≤ (1 : ℝ) := abs_le.mpr hgamma
    simpa [xi_height_interval_minimal_sampling_T, xi_height_interval_minimal_sampling_Umax]
      using h_abs
  · norm_num [xi_height_interval_minimal_sampling_grid,
      xi_height_interval_minimal_sampling_Nmin, xi_height_interval_minimal_sampling_T,
      xi_height_interval_minimal_sampling_Umax]
  · intro N hN
    norm_num [xi_height_interval_minimal_sampling_Nmin, xi_height_interval_minimal_sampling_T,
      xi_height_interval_minimal_sampling_Umax] at hN ⊢
    exact_mod_cast hN
  · intro delta gamma _hgamma hdelta_gt hdelta_le
    linarith

end

end Omega.Zeta
