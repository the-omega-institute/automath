import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Concrete convergence data for
`thm:xi-time-part9za-window6-gff-scaling-lift-invariance`.

The visible centered observable has a limit, while the lifted centered observable differs from it
by an error that vanishes on the separated scale. -/
structure xi_time_part9za_window6_gff_scaling_lift_invariance_data where
  xi_time_part9za_window6_gff_scaling_lift_invariance_visible_centered : ℕ → ℝ
  xi_time_part9za_window6_gff_scaling_lift_invariance_lifted_centered : ℕ → ℝ
  xi_time_part9za_window6_gff_scaling_lift_invariance_limit : ℝ
  xi_time_part9za_window6_gff_scaling_lift_invariance_mesh : ℕ → ℝ
  xi_time_part9za_window6_gff_scaling_lift_invariance_scale : ℕ → ℝ
  xi_time_part9za_window6_gff_scaling_lift_invariance_visible_limit :
    Tendsto xi_time_part9za_window6_gff_scaling_lift_invariance_visible_centered atTop
      (𝓝 xi_time_part9za_window6_gff_scaling_lift_invariance_limit)
  xi_time_part9za_window6_gff_scaling_lift_invariance_lift_collapse_error :
    Tendsto
      (fun m =>
        xi_time_part9za_window6_gff_scaling_lift_invariance_lifted_centered m -
          xi_time_part9za_window6_gff_scaling_lift_invariance_visible_centered m)
      atTop (𝓝 0)
  xi_time_part9za_window6_gff_scaling_lift_invariance_scale_separation :
    Tendsto
      (fun m =>
        xi_time_part9za_window6_gff_scaling_lift_invariance_mesh m /
          xi_time_part9za_window6_gff_scaling_lift_invariance_scale m)
      atTop (𝓝 0)

namespace xi_time_part9za_window6_gff_scaling_lift_invariance_data

/-- The lifted centered observable has the same scaling limit as the visible observable. -/
def xi_time_part9za_window6_gff_scaling_lift_invariance_lift_limit
    (D : xi_time_part9za_window6_gff_scaling_lift_invariance_data) : Prop :=
  Tendsto D.xi_time_part9za_window6_gff_scaling_lift_invariance_lifted_centered atTop
    (𝓝 D.xi_time_part9za_window6_gff_scaling_lift_invariance_limit)

end xi_time_part9za_window6_gff_scaling_lift_invariance_data

/-- Paper label: `thm:xi-time-part9za-window6-gff-scaling-lift-invariance`. -/
theorem paper_xi_time_part9za_window6_gff_scaling_lift_invariance
    (D : xi_time_part9za_window6_gff_scaling_lift_invariance_data) :
    D.xi_time_part9za_window6_gff_scaling_lift_invariance_lift_limit := by
  have hsum :=
    D.xi_time_part9za_window6_gff_scaling_lift_invariance_lift_collapse_error.add
      D.xi_time_part9za_window6_gff_scaling_lift_invariance_visible_limit
  have hsum_limit :
      Tendsto
        (fun m =>
          D.xi_time_part9za_window6_gff_scaling_lift_invariance_lifted_centered m -
              D.xi_time_part9za_window6_gff_scaling_lift_invariance_visible_centered m +
            D.xi_time_part9za_window6_gff_scaling_lift_invariance_visible_centered m)
        atTop (𝓝 D.xi_time_part9za_window6_gff_scaling_lift_invariance_limit) := by
    simpa using hsum
  exact hsum_limit.congr' (by
    filter_upwards with m
    ring)

end Omega.Zeta
