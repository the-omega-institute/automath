import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40CollisionAllReal

namespace Omega.SyncKernelRealInput

/-- The critical quintic controlling the RH-window endpoint for the real-input-`40` collision
package. -/
def real_input_40_collision_rhk_window_critical_quintic (u : ℝ) : ℝ :=
  u ^ 5 + 4 * u ^ 4 + 3 * u ^ 3 - 96 * u ^ 2 - 42 * u - 14

/-- The kernel-RH window is encoded by the nonpositivity of the critical quintic. -/
def real_input_40_collision_rhk_window_kernel_rh (u : ℝ) : Prop :=
  real_input_40_collision_rhk_window_critical_quintic u ≤ 0

private lemma real_input_40_collision_rhk_window_critical_quintic_continuous :
    Continuous real_input_40_collision_rhk_window_critical_quintic := by
  unfold real_input_40_collision_rhk_window_critical_quintic
  continuity

private lemma real_input_40_collision_rhk_window_critical_quintic_neg_three :
    real_input_40_collision_rhk_window_critical_quintic 3 < 0 := by
  norm_num [real_input_40_collision_rhk_window_critical_quintic]

private lemma real_input_40_collision_rhk_window_critical_quintic_pos_four :
    0 < real_input_40_collision_rhk_window_critical_quintic 4 := by
  norm_num [real_input_40_collision_rhk_window_critical_quintic]

private lemma real_input_40_collision_rhk_window_critical_quintic_neg_of_pos_le_three
    {u : ℝ} (hu : 0 < u) (hu3 : u ≤ 3) :
    real_input_40_collision_rhk_window_critical_quintic u < 0 := by
  unfold real_input_40_collision_rhk_window_critical_quintic
  have hpoly :
      u ^ 5 + 4 * u ^ 4 + 3 * u ^ 3 = u ^ 3 * (u ^ 2 + 4 * u + 3) := by
    ring
  have hfactor_bound : u ^ 2 + 4 * u + 3 ≤ 24 := by
    nlinarith
  have hupper : u ^ 5 + 4 * u ^ 4 + 3 * u ^ 3 ≤ 24 * u ^ 3 := by
    rw [hpoly]
    nlinarith [pow_nonneg hu.le 3]
  have hle :
      u ^ 5 + 4 * u ^ 4 + 3 * u ^ 3 - 96 * u ^ 2 - 42 * u - 14 ≤
        24 * u ^ 3 - 96 * u ^ 2 - 42 * u - 14 := by
    linarith
  have hneg_rhs : 24 * u ^ 3 - 96 * u ^ 2 - 42 * u - 14 < 0 := by
    have hu4 : u - 4 ≤ -1 := by linarith
    nlinarith [sq_nonneg u, hu]
  linarith

private lemma real_input_40_collision_rhk_window_critical_quintic_strictMonoOn :
    StrictMonoOn real_input_40_collision_rhk_window_critical_quintic (Set.Ici 3) := by
  intro x hx y hy hxy
  have hfactor :
      real_input_40_collision_rhk_window_critical_quintic y -
          real_input_40_collision_rhk_window_critical_quintic x =
        (y - x) *
          (x ^ 4 + x ^ 3 * y + 4 * x ^ 3 + x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + 3 * x ^ 2 +
            x * y ^ 3 + 4 * x * y ^ 2 + 3 * x * y - 96 * x + y ^ 4 + 4 * y ^ 3 + 3 * y ^ 2 -
            96 * y - 42) := by
    unfold real_input_40_collision_rhk_window_critical_quintic
    ring
  have hx3 : 0 ≤ x - 3 := sub_nonneg.mpr hx
  have hy3 : 0 ≤ y - 3 := sub_nonneg.mpr hy
  have hbracket :
      0 <
        x ^ 4 + x ^ 3 * y + 4 * x ^ 3 + x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + 3 * x ^ 2 +
          x * y ^ 3 + 4 * x * y ^ 2 + 3 * x * y - 96 * x + y ^ 4 + 4 * y ^ 3 + 3 * y ^ 2 -
          96 * y - 42 := by
    have hexpand :
        x ^ 4 + x ^ 3 * y + 4 * x ^ 3 + x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + 3 * x ^ 2 +
            x * y ^ 3 + 4 * x * y ^ 2 + 3 * x * y - 96 * x + y ^ 4 + 4 * y ^ 3 + 3 * y ^ 2 -
            96 * y - 42 =
          (x - 3) ^ 4 + (x - 3) ^ 3 * (y - 3) + 19 * (x - 3) ^ 3 +
            (x - 3) ^ 2 * (y - 3) ^ 2 + 19 * (x - 3) ^ 2 * (y - 3) + 141 * (x - 3) ^ 2 +
            (x - 3) * (y - 3) ^ 3 + 19 * (x - 3) * (y - 3) ^ 2 +
            141 * (x - 3) * (y - 3) + 417 * (x - 3) + (y - 3) ^ 4 + 19 * (y - 3) ^ 3 +
            141 * (y - 3) ^ 2 + 417 * (y - 3) + 300 := by
      ring
    rw [hexpand]
    positivity
  have hpos :
      0 <
        real_input_40_collision_rhk_window_critical_quintic y -
          real_input_40_collision_rhk_window_critical_quintic x := by
    rw [hfactor]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  linarith

/-- Paper label: `prop:real-input-40-collision-rhk-window`. The RH-window endpoint is the unique
positive root of the critical quintic, and the corresponding window is exactly the positive region
where that quintic is nonpositive. -/
theorem paper_real_input_40_collision_rhk_window :
    (∀ u : ℝ, 0 < u → 0 < 4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8) ∧
      ∃! uR : ℝ,
        1 < uR ∧
          real_input_40_collision_rhk_window_critical_quintic uR = 0 ∧
          ∀ u : ℝ, 0 < u →
            (real_input_40_collision_rhk_window_kernel_rh u ↔ u ≤ uR) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    exact (paper_real_input_40_collision_all_real u hu).1
  · have hzero_mem :
        (0 : ℝ) ∈
          Set.Ioo
            (real_input_40_collision_rhk_window_critical_quintic 3)
            (real_input_40_collision_rhk_window_critical_quintic 4) := by
      exact ⟨real_input_40_collision_rhk_window_critical_quintic_neg_three,
        real_input_40_collision_rhk_window_critical_quintic_pos_four⟩
    rcases intermediate_value_Ioo (show (3 : ℝ) ≤ 4 by norm_num)
        real_input_40_collision_rhk_window_critical_quintic_continuous.continuousOn hzero_mem with
      ⟨uR, huRmem, huRroot⟩
    have huRgt1 : 1 < uR := by
      linarith [huRmem.1]
    have hwindow :
        ∀ u : ℝ, 0 < u →
          (real_input_40_collision_rhk_window_kernel_rh u ↔ u ≤ uR) := by
      intro u hu
      constructor
      · intro hk
        by_contra hle
        have huRltu : uR < u := by linarith
        have huge : 3 ≤ u := by linarith [huRmem.1]
        have hmono :
            real_input_40_collision_rhk_window_critical_quintic uR <
              real_input_40_collision_rhk_window_critical_quintic u :=
          real_input_40_collision_rhk_window_critical_quintic_strictMonoOn
            (le_of_lt huRmem.1) huge huRltu
        have hpos :
            0 < real_input_40_collision_rhk_window_critical_quintic u := by
          linarith [huRroot, hmono]
        exact not_lt_of_ge hk hpos
      · intro hle
        by_cases hu3 : u ≤ 3
        · exact le_of_lt
            (real_input_40_collision_rhk_window_critical_quintic_neg_of_pos_le_three hu hu3)
        · have huge : 3 ≤ u := by linarith
          by_cases hueq : u = uR
          · simpa [real_input_40_collision_rhk_window_kernel_rh, hueq, huRroot]
          · have hlt : u < uR := lt_of_le_of_ne hle hueq
            have hmono :
                real_input_40_collision_rhk_window_critical_quintic u <
                  real_input_40_collision_rhk_window_critical_quintic uR :=
              real_input_40_collision_rhk_window_critical_quintic_strictMonoOn
                huge (le_of_lt huRmem.1) hlt
            exact le_of_lt (by linarith [huRroot, hmono])
    refine ⟨uR, ⟨huRgt1, huRroot, hwindow⟩, ?_⟩
    intro uR' huR'
    rcases huR' with ⟨huR'gt1, huR'root, hwindow'⟩
    have huRpos : 0 < uR := by linarith
    have huR'pos : 0 < uR' := by linarith
    have hle : uR ≤ uR' := by
      exact (hwindow' uR huRpos).1
        (by simpa [real_input_40_collision_rhk_window_kernel_rh, huRroot])
    have hge : uR' ≤ uR := by
      exact (hwindow uR' huR'pos).1
        (by simpa [real_input_40_collision_rhk_window_kernel_rh, huR'root])
    linarith

end Omega.SyncKernelRealInput
