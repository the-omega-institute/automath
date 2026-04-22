import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppRhIffDiskZeroFree

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic
open AppRhIffDiskZeroFreeData

/-- The noisy three-point second difference `W_h^ε(x)`. -/
def xi_time_part9zq_threepoint_jensen_rh_disproof_noisy_second_difference
    (Jε : ℝ → ℝ) (x h : ℝ) : ℝ :=
  Jε (x + h) - 2 * Jε x + Jε (x - h)

/-- The explicit `9zq` witness inequality `W_h^ε(x) > 4 ε`. -/
def xi_time_part9zq_threepoint_jensen_rh_disproof_witness
    (Jε : ℝ → ℝ) (x h ε : ℝ) : Prop :=
  4 * ε < xi_time_part9zq_threepoint_jensen_rh_disproof_noisy_second_difference Jε x h

/-- Paper label: `thm:xi-time-part9zq-threepoint-jensen-rh-disproof`. Once the noisy three-point
Jensen witness produces a disk zero, the disk-zero-free RH wrapper gives the contradiction
immediately. -/
theorem paper_xi_time_part9zq_threepoint_jensen_rh_disproof
    (D : AppRhIffDiskZeroFreeData) (Jε : ℝ → ℝ) (x h ε : ℝ)
    (hdisk_zero_of_witness :
      xi_time_part9zq_threepoint_jensen_rh_disproof_witness Jε x h ε →
        ∃ w : D.DiskPoint, D.insideDisk w ∧ D.diskModel w = 0)
    (hwitness : xi_time_part9zq_threepoint_jensen_rh_disproof_witness Jε x h ε) :
    ¬ D.riemannHypothesis := by
  intro hRH
  have hzeroFree : D.diskZeroFree := (paper_app_rh_iff_disk_zero_free D).1 hRH
  rcases hdisk_zero_of_witness hwitness with ⟨w, hwInside, hwZero⟩
  exact hzeroFree w hwInside hwZero

end Omega.Zeta
