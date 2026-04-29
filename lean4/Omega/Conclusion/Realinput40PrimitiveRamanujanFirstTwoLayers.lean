import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-realinput40-primitive-ramanujan-first-two-layers`. -/
theorem paper_conclusion_realinput40_primitive_ramanujan_first_two_layers (r : ℕ)
    (hr : 3 ≤ r) : ¬ r ∣ 2 := by
  intro hdiv
  have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  omega

end Omega.Conclusion
