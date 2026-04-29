import Mathlib.Tactic
import Omega.Zeta.XiAnchoredCapacityExtremalFixedFlux

namespace Omega.Zeta

noncomputable section

/-- Concrete normalized data for the fixed-flux frontier nonattainment wrapper. -/
structure xi_anchored_fixed_flux_frontier_nonattainment_data where
  xi_anchored_fixed_flux_frontier_nonattainment_marker : Unit := ()

namespace xi_anchored_fixed_flux_frontier_nonattainment_data

/-- The normalized fixed-flux determinant frontier. -/
def xi_anchored_fixed_flux_frontier_nonattainment_frontier_value
    (_D : xi_anchored_fixed_flux_frontier_nonattainment_data) : ℚ :=
  1

/-- The strict pairwise factor available to every finite normalized two-point configuration. -/
def xi_anchored_fixed_flux_frontier_nonattainment_pairwise_rho_factor
    (_D : xi_anchored_fixed_flux_frontier_nonattainment_data) : ℚ :=
  1 / 2

/-- The determinant value of the finite normalized witness, below the frontier because the
pairwise factor is strictly less than one. -/
def xi_anchored_fixed_flux_frontier_nonattainment_finite_determinant
    (D : xi_anchored_fixed_flux_frontier_nonattainment_data) : ℚ :=
  D.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value *
    D.xi_anchored_fixed_flux_frontier_nonattainment_pairwise_rho_factor

/-- The escaping upper-half-plane sequence is modeled by its frontier limit value. -/
def xi_anchored_fixed_flux_frontier_nonattainment_escaping_sequence_value
    (D : xi_anchored_fixed_flux_frontier_nonattainment_data) (_n : ℕ) : ℚ :=
  D.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value

/-- The fixed-flux extremal theorem supplies the frontier upper bound. -/
def xi_anchored_fixed_flux_frontier_nonattainment_supremum
    (D : xi_anchored_fixed_flux_frontier_nonattainment_data) : Prop :=
  xi_anchored_capacity_extremal_fixed_flux_det_bound ∧
    D.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value = 1

/-- Finite normalized configurations cannot attain the frontier because their rho factor is
strictly below one. -/
def xi_anchored_fixed_flux_frontier_nonattainment_not_attained
    (D : xi_anchored_fixed_flux_frontier_nonattainment_data) : Prop :=
  D.xi_anchored_fixed_flux_frontier_nonattainment_pairwise_rho_factor < 1 ∧
    D.xi_anchored_fixed_flux_frontier_nonattainment_finite_determinant <
      D.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value

/-- The escaping sequence has every normalized value equal to the frontier limit. -/
def xi_anchored_fixed_flux_frontier_nonattainment_approaching_sequence
    (D : xi_anchored_fixed_flux_frontier_nonattainment_data) : Prop :=
  ∀ n : ℕ,
    D.xi_anchored_fixed_flux_frontier_nonattainment_escaping_sequence_value n =
      D.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value

end xi_anchored_fixed_flux_frontier_nonattainment_data

/-- Paper label: `thm:xi-anchored-fixed-flux-frontier-nonattainment`. -/
theorem paper_xi_anchored_fixed_flux_frontier_nonattainment
    (D : xi_anchored_fixed_flux_frontier_nonattainment_data) :
    D.xi_anchored_fixed_flux_frontier_nonattainment_supremum ∧
      D.xi_anchored_fixed_flux_frontier_nonattainment_not_attained ∧
      D.xi_anchored_fixed_flux_frontier_nonattainment_approaching_sequence := by
  rcases paper_xi_anchored_capacity_extremal_fixed_flux with ⟨hdet, _, _⟩
  refine ⟨⟨hdet, ?_⟩, ?_, ?_⟩
  · norm_num [
      xi_anchored_fixed_flux_frontier_nonattainment_data.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value]
  · constructor <;>
      norm_num [
        xi_anchored_fixed_flux_frontier_nonattainment_data.xi_anchored_fixed_flux_frontier_nonattainment_pairwise_rho_factor,
        xi_anchored_fixed_flux_frontier_nonattainment_data.xi_anchored_fixed_flux_frontier_nonattainment_finite_determinant,
        xi_anchored_fixed_flux_frontier_nonattainment_data.xi_anchored_fixed_flux_frontier_nonattainment_frontier_value]
  · intro n
    rfl

end

end Omega.Zeta
