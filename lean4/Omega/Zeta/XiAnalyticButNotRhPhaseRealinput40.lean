import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedCollisionPressureSingularRing
import Omega.SyncKernelRealInput.RealInput40CollisionRhkWindow

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-analytic-but-not-rh-phase-realinput40`. Past the logarithm of the
unique real-input-`40` RH-window endpoint, the exponential real input remains inside the recorded
analytic singular-ring radius but no longer lies in the RH window. -/
theorem paper_xi_analytic_but_not_rh_phase_realinput40 :
    ∃ uR : ℝ, 1 < uR ∧
      Real.log uR <
        Omega.DerivedConsequences.derived_collision_pressure_singular_ring_nearest_radius ∧
      ∀ θ : ℝ, Real.log uR < θ →
        θ < Omega.DerivedConsequences.derived_collision_pressure_singular_ring_nearest_radius →
        ¬ Omega.SyncKernelRealInput.real_input_40_collision_rhk_window_kernel_rh (Real.exp θ) := by
  rcases Omega.SyncKernelRealInput.paper_real_input_40_collision_rhk_window with ⟨_, huniq⟩
  rcases huniq with ⟨uR, huR, _huR_unique⟩
  rcases huR with ⟨huR_gt_one, _huR_root, hwindow⟩
  have huR_pos : 0 < uR := by linarith
  have hrad :
      Omega.DerivedConsequences.derived_collision_pressure_singular_ring_nearest_radius =
        2.76230289346087 := by
    rcases Omega.DerivedConsequences.paper_derived_collision_pressure_singular_ring with
      ⟨_, _, _, _, _, _, _, _, hrad⟩
    exact hrad
  have huR_lt_fifteen_fourths : uR < (15 / 4 : ℝ) := by
    by_contra hnot
    have hle : (15 / 4 : ℝ) ≤ uR := le_of_not_gt hnot
    have hkernel :
        Omega.SyncKernelRealInput.real_input_40_collision_rhk_window_kernel_rh (15 / 4 : ℝ) := by
      exact (hwindow (15 / 4 : ℝ) (by norm_num)).2 hle
    norm_num [Omega.SyncKernelRealInput.real_input_40_collision_rhk_window_kernel_rh,
      Omega.SyncKernelRealInput.real_input_40_collision_rhk_window_critical_quintic] at hkernel
  have hlog_lt_fifteen_fourths : Real.log uR < Real.log (15 / 4 : ℝ) :=
    Real.log_lt_log huR_pos huR_lt_fifteen_fourths
  have hlog_fifteen_fourths_lt : Real.log (15 / 4 : ℝ) < (11 / 4 : ℝ) := by
    have hlt :=
      Real.log_lt_sub_one_of_pos (show 0 < (15 / 4 : ℝ) by norm_num)
        (show (15 / 4 : ℝ) ≠ 1 by norm_num)
    norm_num at hlt ⊢
    exact hlt
  have hlog_uR_lt_radius :
      Real.log uR <
        Omega.DerivedConsequences.derived_collision_pressure_singular_ring_nearest_radius := by
    rw [hrad]
    exact lt_trans (lt_trans hlog_lt_fifteen_fourths hlog_fifteen_fourths_lt) (by norm_num)
  refine ⟨uR, huR_gt_one, hlog_uR_lt_radius, ?_⟩
  intro θ hθ _hθ_radius hkernel
  have hexp_gt_uR : uR < Real.exp θ := by
    have hexp := Real.exp_lt_exp.mpr hθ
    simpa [Real.exp_log huR_pos] using hexp
  have hexp_le_uR : Real.exp θ ≤ uR :=
    (hwindow (Real.exp θ) (Real.exp_pos θ)).1 hkernel
  exact not_le_of_gt hexp_gt_uR hexp_le_uR

end

end Omega.Zeta
