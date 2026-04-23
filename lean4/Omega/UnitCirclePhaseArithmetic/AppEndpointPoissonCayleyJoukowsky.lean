import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppCayleyUpperhalfDisk
import Omega.UnitCirclePhaseArithmetic.FibUnitCircleUpliftIdentity

namespace Omega.UnitCirclePhaseArithmetic

theorem paper_app_endpoint_poisson_cayley_joukowsky (w : ℂ) (hw : ‖w‖ < 1) :
    let t := Omega.UnitCirclePhaseArithmetic.appCayleyUpperHalfInv w
    Complex.im t = (1 - Complex.normSq w) / Complex.normSq (1 + w) ∧
      ‖Omega.UnitCirclePhaseArithmetic.leyangJ w‖ = ‖w‖ / Complex.normSq (1 + w) ∧
      ‖Omega.UnitCirclePhaseArithmetic.leyangJ w‖ =
        (‖w‖ / (1 - Complex.normSq w)) * Complex.im t := by
  dsimp [Omega.UnitCirclePhaseArithmetic.appCayleyUpperHalfInv]
  have hw_sq : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hw, norm_nonneg w]
  have hw_ne_neg_one : w ≠ -(1 : ℂ) := by
    intro hw1
    have hnorm : ‖w‖ = 1 := by simp [hw1]
    linarith
  have hplus_ne : 1 + w ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero, add_comm] using hw_ne_neg_one
  have hnorm_den_pos : 0 < Complex.normSq (1 + w) := Complex.normSq_pos.2 hplus_ne
  have hnorm_den_ne : Complex.normSq (1 + w) ≠ 0 := hnorm_den_pos.ne'
  have him :
      Complex.im (Complex.I * (1 - w) / (1 + w)) =
        (1 - Complex.normSq w) / Complex.normSq (1 + w) := by
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    ring
  have hleyang :
      ‖Omega.UnitCirclePhaseArithmetic.leyangJ w‖ = ‖w‖ / Complex.normSq (1 + w) := by
    rw [Omega.UnitCirclePhaseArithmetic.leyangJ, norm_div, norm_neg, norm_pow,
      Complex.normSq_eq_norm_sq]
  have hnum_pos : 0 < 1 - Complex.normSq w := by linarith
  refine ⟨him, hleyang, ?_⟩
  rw [hleyang, him]
  field_simp [hnum_pos.ne', hnorm_den_ne]

end Omega.UnitCirclePhaseArithmetic
