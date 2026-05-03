import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-localized-anomaly-strictly-pairwise-quadratic-growth`. -/
theorem paper_conclusion_localized_anomaly_strictly_pairwise_quadratic_growth (r : ℕ)
    (hr : 4 ≤ r) :
    r < Nat.choose r 2 := by
  rw [Nat.choose_two_right]
  rw [← Nat.add_one_le_iff]
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  have hsub : 3 ≤ r - 1 := by omega
  have hmul : r * 3 ≤ r * (r - 1) := Nat.mul_le_mul_left r hsub
  have hlin : (r + 1) * 2 ≤ r * 3 := by omega
  exact le_trans hlin hmul

end Omega.Conclusion
