import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-frozen-escort-integer-renyi-collapse`. -/
theorem paper_conclusion_frozen_escort_integer_renyi_collapse
    (P : ℝ → ℝ) (a ac α g : ℝ) (b : ℕ) (hb : 2 ≤ b) (ha : ac < a)
    (hfreeze_a : P a = a * α + g)
    (hfreeze_ab : P (a * (b : ℝ)) = (a * (b : ℝ)) * α + g) :
    (P (a * (b : ℝ)) - (b : ℝ) * P a) / (1 - (b : ℝ)) = g := by
  have _ha_region : ac < a := ha
  rw [hfreeze_ab, hfreeze_a]
  have hb_ne : 1 - (b : ℝ) ≠ 0 := by
    have hb_real : (1 : ℝ) < b := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hb)
    nlinarith
  field_simp [hb_ne]
  ring

end Omega.Conclusion
