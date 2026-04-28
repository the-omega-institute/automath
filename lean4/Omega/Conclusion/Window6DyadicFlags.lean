import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-680085-dyadic-flags`. -/
theorem paper_conclusion_window6_680085_dyadic_flags :
    (((2 ^ 8 - 1) * (2 ^ 8 - 2) * (2 ^ 8 - 2 ^ 2)) /
      ((2 ^ 3 - 1) * (2 ^ 3 - 2) * (2 ^ 3 - 2 ^ 2))) *
      ((2 ^ 3 - 1) / (2 - 1)) = 680085 := by
  native_decide

end Omega.Conclusion
