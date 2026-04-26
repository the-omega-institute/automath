import Mathlib.Tactic
import Omega.SyncKernelRealInput.FiniteRhSqrtResonanceGeneral
import Omega.SyncKernelRealInput.RealInput40CollisionRhkWindow

namespace Omega.SyncKernelRealInput

/-- The large-`u` asymptotic branch used in the collision-error phase split. -/
noncomputable def real_input_40_collision_error_phase_large_u_branch (u : ℝ) : ℝ :=
  1 - 1 / u

/-- The paper-facing three-regime phase profile: frozen for `u ≤ 1`, square-root on the RH window,
and asymptotic above the unique RH endpoint. -/
noncomputable def real_input_40_collision_error_phase_beta (u uR : ℝ) : ℝ :=
  if u ≤ 1 then 0 else if u ≤ uR then 1 / 2 else real_input_40_collision_error_phase_large_u_branch u

/-- Paper label: `cor:real-input-40-collision-error-phase`. The existing square-root error wrapper
and the RH-window theorem combine into a three-regime phase split. Below `u = 1` the phase is
frozen, on the RH window it equals the square-root exponent `1/2`, and above the unique endpoint
it is the asymptotic branch `1 - 1 / u`, which approaches `1` from below with gap exactly `1 / u`.
-/
theorem paper_real_input_40_collision_error_phase (D : finite_rh_sqrt_resonance_general_data) :
    finite_rh_sqrt_resonance_general_statement D ∧
      ∃! uR : ℝ,
        1 < uR ∧
          real_input_40_collision_rhk_window_critical_quintic uR = 0 ∧
          (∀ u : ℝ, 0 < u → (real_input_40_collision_rhk_window_kernel_rh u ↔ u ≤ uR)) ∧
          (∀ u : ℝ, 0 < u →
            (u ≤ 1 → real_input_40_collision_error_phase_beta u uR = 0) ∧
              (1 < u → u ≤ uR → real_input_40_collision_error_phase_beta u uR = 1 / 2) ∧
              (uR < u →
                real_input_40_collision_error_phase_beta u uR =
                    real_input_40_collision_error_phase_large_u_branch u ∧
                  0 < 1 - real_input_40_collision_error_phase_beta u uR ∧
                  real_input_40_collision_error_phase_beta u uR < 1)) := by
  refine ⟨paper_finite_rh_sqrt_resonance_general D, ?_⟩
  rcases paper_real_input_40_collision_rhk_window with ⟨_, ⟨uR, huR, huR_unique⟩⟩
  rcases huR with ⟨huR_gt1, huR_root, hwindow⟩
  have hphase :
      ∀ u : ℝ, 0 < u →
        (u ≤ 1 → real_input_40_collision_error_phase_beta u uR = 0) ∧
          (1 < u → u ≤ uR → real_input_40_collision_error_phase_beta u uR = 1 / 2) ∧
          (uR < u →
            real_input_40_collision_error_phase_beta u uR =
                real_input_40_collision_error_phase_large_u_branch u ∧
              0 < 1 - real_input_40_collision_error_phase_beta u uR ∧
              real_input_40_collision_error_phase_beta u uR < 1) := by
    intro u hu
    refine ⟨?_, ?_, ?_⟩
    · intro hu_le_one
      unfold real_input_40_collision_error_phase_beta
      simp [hu_le_one]
    · intro hu_gt_one hu_le_uR
      have hnot_le_one : ¬ u ≤ 1 := not_le.mpr hu_gt_one
      unfold real_input_40_collision_error_phase_beta
      simp [hnot_le_one, hu_le_uR]
    · intro huR_lt_u
      have hnot_le_one : ¬ u ≤ 1 := by
        apply not_le.mpr
        linarith [huR_gt1, huR_lt_u]
      have hnot_le_uR : ¬ u ≤ uR := not_le.mpr huR_lt_u
      have hbeta_eq :
          real_input_40_collision_error_phase_beta u uR =
            real_input_40_collision_error_phase_large_u_branch u := by
        unfold real_input_40_collision_error_phase_beta
        simp [hnot_le_one, hnot_le_uR, real_input_40_collision_error_phase_large_u_branch]
      refine ⟨hbeta_eq, ?_, ?_⟩
      · rw [hbeta_eq, real_input_40_collision_error_phase_large_u_branch]
        have hu_inv_pos : 0 < 1 / u := by positivity
        nlinarith
      · rw [hbeta_eq, real_input_40_collision_error_phase_large_u_branch]
        have hu_inv_pos : 0 < 1 / u := by positivity
        nlinarith
  refine ⟨uR, ⟨huR_gt1, huR_root, hwindow, hphase⟩, ?_⟩
  intro uR' huR'
  rcases huR' with ⟨huR'_gt1, huR'_root, hwindow', _hphase'⟩
  exact huR_unique uR' ⟨huR'_gt1, huR'_root, hwindow'⟩

end Omega.SyncKernelRealInput
