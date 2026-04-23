import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The `2κ - 1` sample window at which the Prony rank defect becomes detectable. -/
def unit_circle_comoving_collision_instability_rank_detection_window (κ : ℕ) : ℕ :=
  2 * κ - 1

/-- The `2κ` sample window needed for full Prony recovery. -/
def unit_circle_comoving_collision_instability_exact_recovery_window (κ : ℕ) : ℕ :=
  2 * κ

/-- The separation-scale factor contributed by a `κ × κ` Vandermonde block. -/
def unit_circle_comoving_collision_instability_vandermonde_scale (κ : ℕ) (ssep : ℝ) : ℝ :=
  ssep ^ (κ - 1)

/-- Quantitative degeneration hypothesis coming from a local inverse map over a near-collision
chart. -/
def unit_circle_comoving_collision_instability_vandermonde_degeneracy
    (κ : ℕ) (ssep L Cκ : ℝ) : Prop :=
  Cκ ≤ unit_circle_comoving_collision_instability_vandermonde_scale κ ssep * L

/-- Paper label: `cor:unit-circle-comoving-collision-instability`. The Prony threshold leaves a
single-sample gap between detection and full recovery, and any quantitative Vandermonde
degeneracy estimate in a near-collision chart converts directly into a separation-dependent lower
bound for the local inverse Lipschitz constant. -/
theorem paper_unit_circle_comoving_collision_instability
    (κ : ℕ) (ssep L Cκ : ℝ) (hκ : 1 ≤ κ) (hssep : 0 < ssep)
    (hdeg :
      unit_circle_comoving_collision_instability_vandermonde_degeneracy κ ssep L Cκ) :
    unit_circle_comoving_collision_instability_rank_detection_window κ + 1 =
      unit_circle_comoving_collision_instability_exact_recovery_window κ ∧
    Cκ / ssep ^ (κ - 1) ≤ L := by
  have hwindow :
      unit_circle_comoving_collision_instability_rank_detection_window κ + 1 =
        unit_circle_comoving_collision_instability_exact_recovery_window κ := by
    unfold unit_circle_comoving_collision_instability_rank_detection_window
    unfold unit_circle_comoving_collision_instability_exact_recovery_window
    have htwo : 1 ≤ 2 * κ := by
      nlinarith
    exact Nat.sub_add_cancel htwo
  have hssep_pow_pos : 0 < ssep ^ (κ - 1) := by
    exact pow_pos hssep _
  have hdeg' : Cκ ≤ L * ssep ^ (κ - 1) := by
    simpa [unit_circle_comoving_collision_instability_vandermonde_degeneracy,
      unit_circle_comoving_collision_instability_vandermonde_scale, mul_comm, mul_left_comm,
      mul_assoc] using hdeg
  refine ⟨hwindow, ?_⟩
  exact (div_le_iff₀ hssep_pow_pos).2 hdeg'

end Omega.UnitCirclePhaseArithmetic
