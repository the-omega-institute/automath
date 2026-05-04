import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-visible-hankel-singular-value-depth-lower-bound`. -/
theorem paper_conclusion_visible_hankel_singular_value_depth_lower_bound
    (N c sigmaMin R depth eta : ℝ) (heta : sigmaMin ^ 2 / R ^ 2 ≤ eta)
    (hdepth : c * eta / N ≤ depth)
    (hmono : c * (sigmaMin ^ 2 / R ^ 2) / N ≤ c * eta / N) :
    c * (sigmaMin ^ 2 / R ^ 2) / N ≤ depth := by
  have _ : sigmaMin ^ 2 / R ^ 2 ≤ eta := heta
  exact hmono.trans hdepth

end Omega.Conclusion
