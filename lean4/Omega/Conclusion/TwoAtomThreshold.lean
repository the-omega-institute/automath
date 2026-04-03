import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable def epsilonCritical : ℝ := Real.goldenRatio / Real.sqrt 5

/-- Positivity of the critical two-atom threshold.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_pos : 0 < epsilonCritical := by
  unfold epsilonCritical
  positivity

/-- The critical threshold lies below 1.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_lt_one : epsilonCritical < 1 := by
  unfold epsilonCritical
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have hsqrt5_gt_one : 1 < Real.sqrt 5 := by
    have hsq : (Real.sqrt 5)^2 = (5 : ℝ) := by
      rw [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]
    nlinarith
  have hφ_lt : Real.goldenRatio < Real.sqrt 5 := by
    rw [Real.goldenRatio]
    nlinarith
  exact (div_lt_one hsqrt5_pos).2 hφ_lt

/-- The critical threshold lies in the open unit interval.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_mem_Ioo : epsilonCritical ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨epsilonCritical_pos, epsilonCritical_lt_one⟩

/-- Square of the critical threshold.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_sq : epsilonCritical^2 = Real.goldenRatio^2 / 5 := by
  unfold epsilonCritical
  rw [div_pow, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]

/-- Quadratic equation satisfied by the critical threshold.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_quadratic :
    5 * epsilonCritical^2 - Real.sqrt 5 * epsilonCritical - 1 = 0 := by
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := by positivity
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  rw [epsilonCritical_sq]
  unfold epsilonCritical
  field_simp [hsqrt5_ne]
  nlinarith [Real.goldenRatio_sq, hsqrt5_sq]

/-- The critical threshold is the unique positive root of the quadratic.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_eq_iff_positive_root {ε : ℝ} :
    ε = epsilonCritical ↔
      0 < ε ∧ 5 * ε ^ 2 - Real.sqrt 5 * ε - 1 = 0 := by
  constructor
  · intro hε
    rw [hε]
    exact ⟨epsilonCritical_pos, epsilonCritical_quadratic⟩
  · rintro ⟨hεpos, hquad⟩
    have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
    have hsqrt5_ne : Real.sqrt 5 ≠ 0 := by positivity
    have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    let x : ℝ := ε * Real.sqrt 5
    have hxpos : 0 < x := by
      dsimp [x]
      exact mul_pos hεpos hsqrt5_pos
    have hxquad : x ^ 2 = x + 1 := by
      dsimp [x]
      nlinarith [hquad, hsqrt5_sq]
    have hfactor : (x - Real.goldenRatio) * (x - Real.goldenConj) = 0 := by
      nlinarith [hxquad, Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]
    have hxeq : x = Real.goldenRatio := by
      rcases mul_eq_zero.mp hfactor with hx | hx
      · exact sub_eq_zero.mp hx
      · exfalso
        have : x = Real.goldenConj := sub_eq_zero.mp hx
        rw [this] at hxpos
        linarith [Real.goldenConj_neg]
    have hxdiv := congrArg (fun y : ℝ => y / Real.sqrt 5) hxeq
    simpa [x, epsilonCritical, hsqrt5_ne] using hxdiv

end Omega.Conclusion
