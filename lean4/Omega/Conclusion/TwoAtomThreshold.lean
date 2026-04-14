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

/-- Lower bound: ε_c > 7/10.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_gt_seven_tenths : (7 : ℝ) / 10 < epsilonCritical := by
  have hε_pos := epsilonCritical_pos
  rw [← Real.sqrt_sq (le_of_lt hε_pos), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 7 / 10)]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [epsilonCritical_sq, Real.goldenRatio_sq]
  -- Goal: (7/10)² < (φ+1)/5
  -- φ = (1+√5)/2, so φ+1 = (3+√5)/2, and (φ+1)/5 = (3+√5)/10
  -- (7/10)² = 49/100. Need: 49/100 < (3+√5)/10, i.e., 49/10 < 3+√5, i.e., √5 > 19/10
  have hφ : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by positivity)
  -- √5 > 19/10: (19/10)² = 361/100 < 5
  have hsqrt5_lb : 19 / 10 < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 19 / 10)]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  nlinarith

/-- Upper bound: ε_c < 3/4.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_lt_three_fourths : epsilonCritical < (3 : ℝ) / 4 := by
  have hε_pos := epsilonCritical_pos
  rw [← Real.sqrt_sq (le_of_lt hε_pos), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 / 4)]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [epsilonCritical_sq, Real.goldenRatio_sq]
  -- Goal: (φ+1)/5 < (3/4)² = 9/16
  -- φ+1 = (3+√5)/2, so (φ+1)/5 = (3+√5)/10
  -- Need: (3+√5)/10 < 9/16, i.e., 16(3+√5) < 90, i.e., 48+16√5 < 90, i.e., √5 < 42/16 = 21/8
  have hφ : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by positivity)
  -- √5 < 21/8: (21/8)² = 441/64 > 5
  have hsqrt5_ub : Real.sqrt 5 < 21 / 8 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 21 / 8)]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  nlinarith

/-- Combined: 0.7 < ε_c < 0.75.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem paper_epsilonCritical_numerical_bounds :
    (7 : ℝ) / 10 < epsilonCritical ∧ epsilonCritical < (3 : ℝ) / 4 :=
  ⟨epsilonCritical_gt_seven_tenths, epsilonCritical_lt_three_fourths⟩

end Omega.Conclusion
