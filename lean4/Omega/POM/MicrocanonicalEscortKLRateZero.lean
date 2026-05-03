import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- Concrete rate data for
`thm:pom-microcanonical-escort-kl-rate-zero`.

The two conditioned KL rates are supplied by the layerwise log-density oscillation estimate.
The unconditioned rate is the conditioned forward rate plus the normalized layer-mass loss. -/
structure pom_microcanonical_escort_kl_rate_zero_data where
  pom_microcanonical_escort_kl_rate_zero_forward_conditioned_rate : ℕ → ℝ
  pom_microcanonical_escort_kl_rate_zero_reverse_conditioned_rate : ℕ → ℝ
  pom_microcanonical_escort_kl_rate_zero_unconditioned_rate : ℕ → ℝ
  pom_microcanonical_escort_kl_rate_zero_log_layer_mass_loss_rate : ℕ → ℝ
  pom_microcanonical_escort_kl_rate_zero_local_log_density_oscillation_bound :
    Tendsto pom_microcanonical_escort_kl_rate_zero_forward_conditioned_rate atTop (𝓝 0) ∧
      Tendsto pom_microcanonical_escort_kl_rate_zero_reverse_conditioned_rate atTop (𝓝 0)
  pom_microcanonical_escort_kl_rate_zero_conditional_normalization :
    ∀ m,
      pom_microcanonical_escort_kl_rate_zero_unconditioned_rate m =
        pom_microcanonical_escort_kl_rate_zero_forward_conditioned_rate m +
          pom_microcanonical_escort_kl_rate_zero_log_layer_mass_loss_rate m
  pom_microcanonical_escort_kl_rate_zero_mass_one_assumption :
    Tendsto pom_microcanonical_escort_kl_rate_zero_log_layer_mass_loss_rate atTop (𝓝 0)

namespace pom_microcanonical_escort_kl_rate_zero_data

/-- The forward conditioned KL rate vanishes. -/
def pom_microcanonical_escort_kl_rate_zero_forward
    (D : pom_microcanonical_escort_kl_rate_zero_data) : Prop :=
  Tendsto D.pom_microcanonical_escort_kl_rate_zero_forward_conditioned_rate atTop (𝓝 0)

/-- The reverse conditioned KL rate vanishes. -/
def pom_microcanonical_escort_kl_rate_zero_reverse
    (D : pom_microcanonical_escort_kl_rate_zero_data) : Prop :=
  Tendsto D.pom_microcanonical_escort_kl_rate_zero_reverse_conditioned_rate atTop (𝓝 0)

/-- The unconditioned KL rate vanishes after the layer mass tends to one. -/
def pom_microcanonical_escort_kl_rate_zero_unconditioned
    (D : pom_microcanonical_escort_kl_rate_zero_data) : Prop :=
  Tendsto D.pom_microcanonical_escort_kl_rate_zero_unconditioned_rate atTop (𝓝 0)

end pom_microcanonical_escort_kl_rate_zero_data

/-- Paper label: `thm:pom-microcanonical-escort-kl-rate-zero`. -/
theorem paper_pom_microcanonical_escort_kl_rate_zero
    (D : pom_microcanonical_escort_kl_rate_zero_data) :
    D.pom_microcanonical_escort_kl_rate_zero_forward ∧
      D.pom_microcanonical_escort_kl_rate_zero_reverse ∧
        D.pom_microcanonical_escort_kl_rate_zero_unconditioned := by
  refine ⟨D.pom_microcanonical_escort_kl_rate_zero_local_log_density_oscillation_bound.1,
    D.pom_microcanonical_escort_kl_rate_zero_local_log_density_oscillation_bound.2, ?_⟩
  have hsum :=
    D.pom_microcanonical_escort_kl_rate_zero_local_log_density_oscillation_bound.1.add
      D.pom_microcanonical_escort_kl_rate_zero_mass_one_assumption
  have hsum_zero :
      Tendsto
        (fun m =>
          D.pom_microcanonical_escort_kl_rate_zero_forward_conditioned_rate m +
            D.pom_microcanonical_escort_kl_rate_zero_log_layer_mass_loss_rate m)
        atTop (𝓝 0) := by
    simpa using hsum
  exact hsum_zero.congr' (by
    filter_upwards with m
    exact (D.pom_microcanonical_escort_kl_rate_zero_conditional_normalization m).symm)

end Omega.POM
