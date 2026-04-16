import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- On the interval `(1/2, 1)`, the scalar identity `p(1-p) = 2p - 1` has the unique solution
`p = φ⁻¹`, with complementary bias `1 - p = φ⁻²`.
    thm:conclusion-golden-bias-second-order-uniqueness -/
theorem paper_conclusion_golden_bias_second_order_uniqueness (p : ℝ)
    (hp : 1 / 2 < p ∧ p < 1) :
    p * (1 - p) = 2 * p - 1 ↔
      p = 1 / Real.goldenRatio ∧ 1 - p = 1 / Real.goldenRatio ^ 2 := by
  have hquadratic : p * (1 - p) = 2 * p - 1 ↔ p ^ 2 + p - 1 = 0 := by
    constructor <;> intro h <;> nlinarith [h]
  constructor
  · intro h
    have hpq : p ^ 2 + p - 1 = 0 := hquadratic.mp h
    have hfactor :
        (p + Real.goldenConj) * (p + Real.goldenRatio) = 0 := by
      nlinarith [hpq, Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]
    have hφ_ne : p + Real.goldenRatio ≠ 0 := by
      have hφ_pos : 0 < p + Real.goldenRatio := by
        linarith [hp.1, Real.goldenRatio_pos]
      linarith
    have hψ : p + Real.goldenConj = 0 := by
      exact Or.resolve_right (mul_eq_zero.mp hfactor) hφ_ne
    have hp_eq : p = 1 / Real.goldenRatio := by
      calc
        p = -Real.goldenConj := by linarith
        _ = Real.goldenRatio⁻¹ := by rw [Real.inv_goldenRatio]
        _ = 1 / Real.goldenRatio := by rw [one_div]
    have hone_sub :
        1 - p = 1 / Real.goldenRatio ^ 2 := by
      have hψsq : Real.goldenConj ^ 2 = 1 / Real.goldenRatio ^ 2 := by
        rw [show (1 : ℝ) / Real.goldenRatio ^ 2 = (Real.goldenRatio⁻¹) ^ 2 by
          rw [one_div, inv_pow]]
        rw [Real.inv_goldenRatio]
        ring
      calc
        1 - p = 1 + Real.goldenConj := by linarith
        _ = Real.goldenConj ^ 2 := by
          rw [Real.goldenConj_sq]
          ring
        _ = 1 / Real.goldenRatio ^ 2 := hψsq
    exact ⟨hp_eq, hone_sub⟩
  · rintro ⟨hp_eq, _⟩
    have hp_root : p = -Real.goldenConj := by
      calc
        p = 1 / Real.goldenRatio := hp_eq
        _ = Real.goldenRatio⁻¹ := by rw [one_div]
        _ = -Real.goldenConj := Real.inv_goldenRatio
    have hpq : p ^ 2 + p - 1 = 0 := by
      rw [hp_root]
      nlinarith [Real.goldenConj_sq]
    exact hquadratic.mpr hpq

end Omega.Conclusion
