import Mathlib.Tactic

namespace Omega.Conclusion

/-- Explicit first and second moments, together with the variance, for the three-valued Burnside
root-count distribution in the `T₅` setting.
    cor:derived-t5-burnside-moments -/
theorem paper_derived_t5_burnside_moments :
    ((0 : ℚ) * (73 / 96) + 4 * (19 / 80) + 24 * (1 / 480) = 1) ∧
      ((0 : ℚ)^2 * (73 / 96) + 4^2 * (19 / 80) + 24^2 * (1 / 480) = 5) ∧
      (5 - 1^2 = 4) := by
  norm_num

end Omega.Conclusion
