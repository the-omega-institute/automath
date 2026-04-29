import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-serrin-ellipsoid-lp-transverse-rigidity`. Matching the axis
intercepts identifies `aᵢ = √λᵢ`, and the two-coordinate boundary point forces the scalar identity
`2 * (1 / √2)^p = 1`; since `1 / √2` lies strictly between `0` and `1`, this happens only for
`p = 2`. -/
theorem paper_conclusion_serrin_ellipsoid_lp_transverse_rigidity
    {n p : ℕ} (hn : 2 ≤ n) (hp : 1 < p) (lam a : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (haxis : ∀ i, a i = Real.sqrt (lam i)) (hboundary : 2 * (1 / Real.sqrt 2) ^ p = 1) :
    p = 2 ∧ ∀ i, a i ^ 2 = lam i := by
  let _ := hn
  have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt2_gt_one : 1 < Real.sqrt 2 := by
    have hsq : (1 : ℝ) ^ 2 < (Real.sqrt 2) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg 2) hsq
  have hx_pos : 0 < 1 / Real.sqrt 2 := by positivity
  have hx_lt_one : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_iff₀ hsqrt2_pos]
    simpa using hsqrt2_gt_one
  have hx_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hscalar : (1 / Real.sqrt 2 : ℝ) ^ p = (1 / Real.sqrt 2 : ℝ) ^ 2 := by
    have hx_two : 2 * ((1 / Real.sqrt 2 : ℝ) ^ 2) = 1 := by
      rw [hx_sq]
      norm_num
    linarith
  have hp_eq_two : p = 2 := by
    by_cases hlt : p < 2
    · have hltpow :
        (1 / Real.sqrt 2 : ℝ) ^ 2 < (1 / Real.sqrt 2 : ℝ) ^ p := by
        exact pow_lt_pow_right_of_lt_one₀ hx_pos hx_lt_one hlt
      exact (hltpow.ne hscalar.symm).elim
    · have hge : 2 ≤ p := Nat.le_of_not_gt hlt
      by_cases hgt : 2 < p
      · have hltpow :
          (1 / Real.sqrt 2 : ℝ) ^ p < (1 / Real.sqrt 2 : ℝ) ^ 2 := by
          exact pow_lt_pow_right_of_lt_one₀ hx_pos hx_lt_one hgt
        exact (hltpow.ne hscalar).elim
      · omega
  refine ⟨hp_eq_two, ?_⟩
  intro i
  rw [haxis i, Real.sq_sqrt (le_of_lt (hlam i))]

end Omega.Conclusion
