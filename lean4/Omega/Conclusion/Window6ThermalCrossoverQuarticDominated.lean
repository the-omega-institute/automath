import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-thermal-crossover-quartic-dominated`. -/
theorem paper_conclusion_window6_thermal_crossover_quartic_dominated
    (x : ℚ) (hx0 : 0 < x) (hlo : (4 : ℚ) / 5 < x) (hhi : x < (13 : ℚ) / 16) :
    (4 : ℚ) / 5 < x ∧ x < (13 : ℚ) / 16 ∧ (27 : ℚ) * x ^ 4 > (21 : ℚ) / 2 := by
  have _hx_nonneg : (0 : ℚ) ≤ x := le_of_lt hx0
  have hbase_nonneg : (0 : ℚ) ≤ 4 / 5 := by norm_num
  have hpow : ((4 : ℚ) / 5) ^ 4 < x ^ 4 :=
    pow_lt_pow_left₀ hlo hbase_nonneg (by norm_num)
  have harith : (21 : ℚ) / 2 < 27 * (((4 : ℚ) / 5) ^ 4) := by norm_num
  have hmul : (27 : ℚ) * (((4 : ℚ) / 5) ^ 4) < 27 * x ^ 4 := by
    nlinarith
  exact ⟨hlo, hhi, by nlinarith⟩

end Omega.Conclusion
