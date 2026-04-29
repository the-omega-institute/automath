import Mathlib.Tactic

namespace Omega.Zeta

/-- Eventual divergence to `+∞`, expressed against real thresholds. -/
def xi_time_part66_zero_density_never_sufficient_eventually_diverges
    (u : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → B < u m

/-- Concrete data for the part-66 zero-density obstruction.  The small parameter
`eta`, the density statistic `Phi`, and the collision scale are actual functions;
boundedness and divergence are stated as concrete analytic bounds. -/
structure xi_time_part66_zero_density_never_sufficient_data where
  eta : ℕ → ℝ
  Phi : ℝ → ℝ
  collisionScale : ℕ → ℝ
  eta_tends_zero :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → |eta m| ≤ ε
  Phi_bounded_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ x : ℝ, |x| ≤ ε → Phi x ≤ B
  collision_scale_diverges :
    xi_time_part66_zero_density_never_sufficient_eventually_diverges collisionScale

/-- Eventually the collision scale is larger than a uniform density-based bound
available from boundedness of `Phi` near zero. -/
def xi_time_part66_zero_density_never_sufficient_data.eventual_collision_scale_exceeds_density_bound
    (D : xi_time_part66_zero_density_never_sufficient_data) : Prop :=
  ∃ B : ℝ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → D.Phi (D.eta m) ≤ B ∧ B < D.collisionScale m

/-- thm:xi-time-part66-zero-density-never-sufficient -/
theorem paper_xi_time_part66_zero_density_never_sufficient
    (D : xi_time_part66_zero_density_never_sufficient_data) :
    D.eventual_collision_scale_exceeds_density_bound := by
  rcases D.Phi_bounded_near_zero with ⟨ε, hε, B, hB⟩
  rcases D.eta_tends_zero ε hε with ⟨Nη, hη⟩
  rcases D.collision_scale_diverges B with ⟨Nc, hc⟩
  refine ⟨B, max Nη Nc, ?_⟩
  intro m hm
  have hmη : Nη ≤ m := le_trans (Nat.le_max_left Nη Nc) hm
  have hmc : Nc ≤ m := le_trans (Nat.le_max_right Nη Nc) hm
  exact ⟨hB (D.eta m) (hη m hmη), hc m hmc⟩

end Omega.Zeta
