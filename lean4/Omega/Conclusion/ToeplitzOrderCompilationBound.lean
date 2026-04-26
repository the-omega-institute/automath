import Mathlib

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-toeplitz-order-compilation-bound`. -/
theorem paper_conclusion_toeplitz_order_compilation_bound (N : Nat) (eta beta r : Real)
    (hr0 : 0 < r) (hr1 : r < 1) (hbeta : 0 < beta) (hbetalt : beta < eta)
    (hN : (N + 1 : Real) >= Real.log ((eta + beta) / (eta - beta)) / (-Real.log r)) :
    eta >= beta * (1 + r ^ (N + 1)) / (1 - r ^ (N + 1)) := by
  set x : ℝ := r ^ (N + 1)
  have heta_pos : 0 < eta := by linarith
  have hratio_pos : 0 < (eta + beta) / (eta - beta) := by
    have hnum_pos : 0 < eta + beta := by linarith
    have hden_pos : 0 < eta - beta := by linarith
    exact div_pos hnum_pos hden_pos
  have hratio_inv_pos : 0 < (eta - beta) / (eta + beta) := by
    have hnum_pos : 0 < eta - beta := by linarith
    have hden_pos : 0 < eta + beta := by linarith
    exact div_pos hnum_pos hden_pos
  have hneglog_pos : 0 < -Real.log r := by
    have hlog_neg : Real.log r < 0 := Real.log_neg hr0 hr1
    linarith
  have hlog_ratio_le :
      Real.log ((eta + beta) / (eta - beta)) ≤ (N + 1 : ℝ) * (-Real.log r) := by
    exact (div_le_iff₀ hneglog_pos).mp hN
  have hlog_x_le :
      Real.log x ≤ Real.log ((eta - beta) / (eta + beta)) := by
    have hlog_x :
        Real.log x = ((N : ℝ) + 1) * Real.log r := by
      rw [show x = r ^ (N + 1) by rfl, ← Real.rpow_natCast, Real.log_rpow hr0]
      simp [Nat.cast_add]
    have hlog_inv :
        Real.log ((eta - beta) / (eta + beta)) =
          -Real.log ((eta + beta) / (eta - beta)) := by
      rw [show (eta - beta) / (eta + beta) = ((eta + beta) / (eta - beta))⁻¹ by field_simp]
      simpa using Real.log_inv ((eta + beta) / (eta - beta))
    rw [hlog_x, hlog_inv]
    linarith
  have hx_le :
      x ≤ (eta - beta) / (eta + beta) := by
    have hx_pos : 0 < x := by
      simp [x, pow_pos hr0]
    have h := Real.exp_le_exp.mpr hlog_x_le
    simpa [Real.exp_log hx_pos, Real.exp_log hratio_inv_pos] using h
  have hx_lt_one : x < 1 := by
    simpa [x] using pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero N)
  have hone_sub_pos : 0 < 1 - x := by
    linarith
  have hcross :
      x * (eta + beta) ≤ eta - beta := by
    have heta_beta_pos : 0 < eta + beta := by linarith
    exact (le_div_iff₀ heta_beta_pos).mp hx_le
  have hmain : beta * (1 + x) ≤ eta * (1 - x) := by
    nlinarith
  have hfinal : beta * (1 + x) / (1 - x) ≤ eta := by
    exact (div_le_iff₀ hone_sub_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)
  simpa [x] using hfinal

end Omega.Conclusion
