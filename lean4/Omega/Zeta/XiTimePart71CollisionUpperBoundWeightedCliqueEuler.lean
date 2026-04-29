import Mathlib.Tactic
import Omega.Zeta.XiTimePart71ZeroSpectrumWeightedCliqueEuler

namespace Omega.Zeta

/-- Collision upper bound read from the zero-spectrum weighted clique Euler package. -/
def xi_time_part71_collision_upper_bound_weighted_clique_euler_collision_upper_bound
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) : Prop :=
  D.zeroSpectrumCard ≤ D.weightedCliqueEulerSum

/-- Triangle-free two-layer simplification: the two finite clique sums have identical support
after the zero-coset nerve is rewritten as its clique complex. -/
def xi_time_part71_collision_upper_bound_weighted_clique_euler_triangle_free_simplification
    (D : xi_time_part71_zero_spectrum_weighted_clique_euler_data) : Prop :=
  D.zeroSpectrumCard = D.weightedCliqueEulerSum

/-- Paper-facing collision package for the finite weighted clique Euler identity. -/
def xi_time_part71_collision_upper_bound_weighted_clique_euler_statement : Prop :=
  ∀ D : xi_time_part71_zero_spectrum_weighted_clique_euler_data,
    xi_time_part71_collision_upper_bound_weighted_clique_euler_collision_upper_bound D ∧
      xi_time_part71_collision_upper_bound_weighted_clique_euler_triangle_free_simplification D

/-- Paper label: `cor:xi-time-part71-collision-upper-bound-weighted-clique-euler`. -/
theorem paper_xi_time_part71_collision_upper_bound_weighted_clique_euler :
    xi_time_part71_collision_upper_bound_weighted_clique_euler_statement := by
  intro D
  have hEuler := paper_xi_time_part71_zero_spectrum_weighted_clique_euler D
  exact ⟨le_of_eq hEuler, hEuler⟩

end Omega.Zeta
