import Omega.Zeta.XiTimePart63bFixedqSchurPacketExactInversion

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete fixed-`q` Schur packet together with the hook-support zero condition for the
single-cycle column. -/
structure xi_time_part63b_qcycle_hook_schur_projection_data where
  q : ℕ
  schur_character : Fin q → Fin q → ℚ
  schur_dimension : Fin q → ℚ
  cycle_weight : Fin q → ℚ
  schur_coordinate : Fin q → ℚ
  collision_coordinate : Fin q → ℚ
  qcycle : Fin q
  is_hook : Fin q → Bool
  schur_dimension_ne_zero : ∀ lam, schur_dimension lam ≠ 0
  cycle_weight_ne_zero : ∀ mu, cycle_weight mu ≠ 0
  forward_tomography :
    ∀ lam,
      schur_coordinate lam / schur_dimension lam =
        ∑ mu, schur_character lam mu / cycle_weight mu * collision_coordinate mu
  column_orthogonality :
    ∀ mu nu,
      ∑ lam, schur_character lam mu * schur_character lam nu =
        if mu = nu then cycle_weight mu else 0
  row_orthogonality :
    ∀ lam nu,
      ∑ mu, schur_character lam mu * schur_character nu mu / cycle_weight mu =
        if lam = nu then 1 else 0
  qcycle_character_zero_of_not_hook :
    ∀ lam, is_hook lam = false → schur_character lam qcycle = 0

/-- The underlying fixed-`q` packet used by the exact Schur inversion theorem. -/
def xi_time_part63b_qcycle_hook_schur_projection_packet
    (D : xi_time_part63b_qcycle_hook_schur_projection_data) :
    xi_time_part63b_fixedq_schur_packet_exact_inversion_data where
  q := D.q
  schur_character := D.schur_character
  schur_dimension := D.schur_dimension
  cycle_weight := D.cycle_weight
  schur_coordinate := D.schur_coordinate
  collision_coordinate := D.collision_coordinate
  schur_dimension_ne_zero := D.schur_dimension_ne_zero
  cycle_weight_ne_zero := D.cycle_weight_ne_zero
  forward_tomography := D.forward_tomography
  column_orthogonality := D.column_orthogonality
  row_orthogonality := D.row_orthogonality

/-- Hook-supported single-cycle Schur projection. -/
def xi_time_part63b_qcycle_hook_schur_projection_hookProjection
    (D : xi_time_part63b_qcycle_hook_schur_projection_data) : ℚ :=
  ∑ lam,
    if D.is_hook lam then
      D.schur_character lam D.qcycle / D.schur_dimension lam * D.schur_coordinate lam
    else
      0

namespace xi_time_part63b_qcycle_hook_schur_projection_data

/-- Paper-facing hook projection claim. -/
def claim (D : xi_time_part63b_qcycle_hook_schur_projection_data) : Prop :=
  xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
      (xi_time_part63b_qcycle_hook_schur_projection_packet D) D.schur_coordinate D.qcycle =
    xi_time_part63b_qcycle_hook_schur_projection_hookProjection D ∧
  xi_time_part63b_qcycle_hook_schur_projection_hookProjection D =
    D.collision_coordinate D.qcycle

end xi_time_part63b_qcycle_hook_schur_projection_data

open xi_time_part63b_qcycle_hook_schur_projection_data

private theorem xi_time_part63b_qcycle_hook_schur_projection_inverse_eq_hookProjection
    (D : xi_time_part63b_qcycle_hook_schur_projection_data) :
    xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
        (xi_time_part63b_qcycle_hook_schur_projection_packet D) D.schur_coordinate D.qcycle =
      xi_time_part63b_qcycle_hook_schur_projection_hookProjection D := by
  unfold xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
  unfold xi_time_part63b_qcycle_hook_schur_projection_hookProjection
  refine Finset.sum_congr rfl ?_
  intro lam hlam
  by_cases hhook : D.is_hook lam
  · simp [xi_time_part63b_qcycle_hook_schur_projection_packet, hhook]
  · have hzero : D.schur_character lam D.qcycle = 0 :=
      D.qcycle_character_zero_of_not_hook lam (Bool.eq_false_iff.mpr hhook)
    simp [xi_time_part63b_qcycle_hook_schur_projection_packet, hhook, hzero]

/-- Paper label: `thm:xi-time-part63b-qcycle-hook-schur-projection`. -/
theorem paper_xi_time_part63b_qcycle_hook_schur_projection
    (D : xi_time_part63b_qcycle_hook_schur_projection_data) : D.claim := by
  have hhook :=
    xi_time_part63b_qcycle_hook_schur_projection_inverse_eq_hookProjection D
  refine ⟨hhook, ?_⟩
  have hD :=
    paper_xi_time_part63b_fixedq_schur_packet_exact_inversion
      (xi_time_part63b_qcycle_hook_schur_projection_packet D)
  rcases hD with ⟨hrecover, _, _⟩
  rw [← hhook]
  exact hrecover D.qcycle

end Omega.Zeta
