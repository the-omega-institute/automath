import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-area-law-page-time-lower-bound`. -/
theorem paper_conclusion_area_law_page_time_lower_bound
    (A logAlphabet worstExpectedTime : ℝ)
    (hReadout : A / (4 * logAlphabet) ≤ worstExpectedTime) :
    A / (4 * logAlphabet) ≤ worstExpectedTime := by
  exact hReadout

end Omega.Conclusion
