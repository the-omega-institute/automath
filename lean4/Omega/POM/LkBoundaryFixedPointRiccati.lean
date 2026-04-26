import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-Lk-boundary-fixed-point-riccati`. -/
theorem paper_pom_lk_boundary_fixed_point_riccati (t q : ℝ) (ht : 0 < t)
    (hq : q = 1 + t / 2 - Real.sqrt (t * (4 + t)) / 2) :
    0 < q ∧ q < 1 ∧ q ^ 2 - (2 + t) * q + 1 = 0 ∧
      ∀ q' : ℝ, 0 < q' → q' < 1 → q' ^ 2 - (2 + t) * q' + 1 = 0 → q' = q := by
  subst q
  let s : ℝ := Real.sqrt (t * (4 + t))
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  have harg_nonneg : 0 ≤ t * (4 + t) := by nlinarith [ht]
  have hs_sq : s ^ 2 = t * (4 + t) := by
    dsimp [s]
    exact Real.sq_sqrt harg_nonneg
  have hs_lt_t_two : s < t + 2 := by
    have hsq_lt : t * (4 + t) < (t + 2) ^ 2 := by nlinarith
    have hsqrt_lt :
        Real.sqrt (t * (4 + t)) < Real.sqrt ((t + 2) ^ 2) :=
      Real.sqrt_lt_sqrt harg_nonneg hsq_lt
    have hsqrt_sq : Real.sqrt ((t + 2) ^ 2) = t + 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ t + 2)]
    simpa [s, hsqrt_sq] using hsqrt_lt
  have ht_lt_s : t < s := by
    have hsq_lt : t ^ 2 < t * (4 + t) := by nlinarith [ht]
    have hsqrt_lt : Real.sqrt (t ^ 2) < Real.sqrt (t * (4 + t)) :=
      Real.sqrt_lt_sqrt (sq_nonneg t) hsq_lt
    have hsqrt_sq : Real.sqrt (t ^ 2) = t := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
    simpa [s, hsqrt_sq] using hsqrt_lt
  have hq_pos : 0 < 1 + t / 2 - s / 2 := by nlinarith
  have hq_lt_one : 1 + t / 2 - s / 2 < 1 := by nlinarith
  have hquad : (1 + t / 2 - s / 2) ^ 2 - (2 + t) * (1 + t / 2 - s / 2) + 1 = 0 := by
    nlinarith [hs_sq]
  refine ⟨by simpa [s] using hq_pos, by simpa [s] using hq_lt_one,
    by simpa [s] using hquad, ?_⟩
  intro q' hq'_pos hq'_lt_one hq'_quad
  have hfactor :
      (q' - (1 + t / 2 - s / 2)) * (q' + (1 + t / 2 - s / 2) - (2 + t)) = 0 := by
    nlinarith [hq'_quad, hquad]
  rcases mul_eq_zero.mp hfactor with hsame | hsum
  · nlinarith
  · exfalso
    have hsum_lt_two : q' + (1 + t / 2 - s / 2) < 2 := by nlinarith
    have hsum_eq : q' + (1 + t / 2 - s / 2) = 2 + t := by nlinarith
    nlinarith [ht]

end

end Omega.POM
