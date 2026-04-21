import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The endpoint `-1` Poisson/Busemann coordinate of the Cayley image recovers the upper
half-plane height. -/
theorem paper_app_busemann_poisson_minus1 (x y : Real) (hy : 0 < y) :
    let t : Complex := (x : Complex) + y * Complex.I
    let w : Complex := (1 + Complex.I * t) / (1 - Complex.I * t)
    (1 - ‖w‖ ^ 2) / ‖1 + w‖ ^ 2 = y := by
  dsimp
  set t : Complex := (x : Complex) + y * Complex.I
  set num : Complex := 1 + Complex.I * t
  set den : Complex := 1 - Complex.I * t
  have hden :
      den ≠ 0 := by
    intro hzero
    have hre : Complex.re den = 1 + y := by
      simp [den, t, mul_add]
    rw [hzero] at hre
    simp at hre
    linarith
  have hnorm_den :
      Complex.normSq den = x ^ 2 + (1 + y) ^ 2 := by
    simp [den, t, Complex.normSq_apply, mul_add, pow_two]
    ring
  have hnorm_num :
      Complex.normSq num = x ^ 2 + (1 - y) ^ 2 := by
    simp [num, t, Complex.normSq_apply, mul_add, pow_two]
    ring
  have hw : ‖num / den‖ ^ 2 = (x ^ 2 + (1 - y) ^ 2) / (x ^ 2 + (1 + y) ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_div, hnorm_num, hnorm_den]
  have hone : 1 + num / den = (2 : Complex) / den := by
    calc
      1 + num / den = den / den + num / den := by rw [div_self hden]
      _ = (den + num) / den := by rw [← add_div]
      _ = (2 : Complex) / den := by
        simp [num, den]
        ring_nf
  have htwo : Complex.normSq (2 : Complex) = 4 := by
    norm_num [Complex.normSq_apply]
  have hone_sq : ‖1 + num / den‖ ^ 2 = 4 / (x ^ 2 + (1 + y) ^ 2) := by
    rw [hone, Complex.sq_norm, Complex.normSq_div, hnorm_den]
    rw [htwo]
  have hpos : 0 < x ^ 2 + (1 + y) ^ 2 := by
    nlinarith [sq_nonneg x, sq_pos_of_ne_zero (show 1 + y ≠ 0 by linarith)]
  rw [hw, hone_sq]
  field_simp [hpos.ne']
  ring

end Omega.UnitCirclePhaseArithmetic
