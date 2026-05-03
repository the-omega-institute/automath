import Omega.Zeta.XiComovingPrefixEndpointBarrierLaw

namespace Omega.Zeta

/-- Concrete inputs for the comoving-prefix rate threshold. -/
structure xi_comoving_prefix_rate_phase_transition_data where
  T : ℝ
  delta0 : ℝ
  r : ℝ
  hdelta0_pos : 0 < delta0
  hdelta0_half : delta0 ≤ 1 / 2

/-- Base-two logarithm used by the prefix law. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_log2 (T : ℝ) : ℝ :=
  Real.log T / Real.log 2

/-- The prescribed prefix depth `B(T) = floor(r log₂ T)`. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_prefix_depth
    (D : xi_comoving_prefix_rate_phase_transition_data) : ℕ :=
  Nat.floor (D.r * xi_comoving_prefix_rate_phase_transition_log2 D.T)

/-- Closed-form endpoint budget at the moving prefix depth. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_closed_budget
    (D : xi_comoving_prefix_rate_phase_transition_data) : ℝ :=
  xiComovingPrefixPmin D.T D.delta0
    (xi_comoving_prefix_rate_phase_transition_prefix_depth D)

/-- The endpoint-barrier closed form after substituting `B(T)`. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_substituted_budget
    (D : xi_comoving_prefix_rate_phase_transition_data) : ℝ :=
  Real.log
      ((((D.T *
              (2 : ℝ) ^
                (-(xi_comoving_prefix_rate_phase_transition_prefix_depth D : ℝ))) ^
            (2 : ℕ)) +
          (1 + D.delta0) ^ (2 : ℕ)) /
        (4 * D.delta0)) /
    Real.log 2

/-- The subcritical concrete regime `0 ≤ r < 1`. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_subcritical_regime
    (D : xi_comoving_prefix_rate_phase_transition_data) : Prop :=
  0 ≤ D.r →
    D.r < 1 →
      xi_comoving_prefix_rate_phase_transition_closed_budget D =
        xi_comoving_prefix_rate_phase_transition_substituted_budget D

/-- The critical concrete regime `r = 1`. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_critical_regime
    (D : xi_comoving_prefix_rate_phase_transition_data) : Prop :=
  D.r = 1 →
    xi_comoving_prefix_rate_phase_transition_closed_budget D =
      xi_comoving_prefix_rate_phase_transition_substituted_budget D

/-- The supercritical concrete regime `r > 1`. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_supercritical_regime
    (D : xi_comoving_prefix_rate_phase_transition_data) : Prop :=
  1 < D.r →
    xi_comoving_prefix_rate_phase_transition_closed_budget D =
      xi_comoving_prefix_rate_phase_transition_substituted_budget D

/-- Concrete three-regime package for the comoving-prefix phase transition threshold. -/
noncomputable def xi_comoving_prefix_rate_phase_transition_three_regimes
    (D : xi_comoving_prefix_rate_phase_transition_data) : Prop :=
  xi_comoving_prefix_rate_phase_transition_prefix_depth D =
      Nat.floor (D.r * xi_comoving_prefix_rate_phase_transition_log2 D.T) ∧
    xi_comoving_prefix_rate_phase_transition_subcritical_regime D ∧
      xi_comoving_prefix_rate_phase_transition_critical_regime D ∧
        xi_comoving_prefix_rate_phase_transition_supercritical_regime D

/-- Paper label: `prop:xi-comoving-prefix-rate-phase-transition`. The moving prefix depth is
`floor(r log₂ T)`, and all three rate regimes inherit the same endpoint closed form from the
barrier law after substituting this depth. -/
theorem paper_xi_comoving_prefix_rate_phase_transition
    (D : xi_comoving_prefix_rate_phase_transition_data) :
    xi_comoving_prefix_rate_phase_transition_three_regimes D := by
  have hbarrier :=
    paper_xi_comoving_prefix_endpoint_barrier_law
      (T := D.T) (δ₀ := D.delta0)
      (B := xi_comoving_prefix_rate_phase_transition_prefix_depth D)
      D.hdelta0_pos D.hdelta0_half
  have hclosed :
      xi_comoving_prefix_rate_phase_transition_closed_budget D =
        xi_comoving_prefix_rate_phase_transition_substituted_budget D := by
    simpa [xi_comoving_prefix_rate_phase_transition_closed_budget,
      xi_comoving_prefix_rate_phase_transition_substituted_budget,
      xi_comoving_prefix_rate_phase_transition_prefix_depth, xiComovingPrefixError] using
      hbarrier.2
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro _hr_nonneg _hr_lt
    exact hclosed
  · intro _hr_eq
    exact hclosed
  · intro _hr_gt
    exact hclosed

end Omega.Zeta
