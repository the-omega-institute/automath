import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-prime-log-unweighted-euler-regular`. -/
theorem paper_conclusion_prime_log_unweighted_euler_regular
    (reciprocalSummable eulerProductAbsolutelyConverges analyticNearOne noMainPole : Prop)
    (hRecip : reciprocalSummable)
    (hEuler : reciprocalSummable → eulerProductAbsolutelyConverges)
    (hAnalytic : eulerProductAbsolutelyConverges → analyticNearOne)
    (hNoPole : analyticNearOne → noMainPole) :
    eulerProductAbsolutelyConverges ∧ analyticNearOne ∧ noMainPole := by
  have hEulerConv : eulerProductAbsolutelyConverges := hEuler hRecip
  have hAnalyticNearOne : analyticNearOne := hAnalytic hEulerConv
  exact ⟨hEulerConv, hAnalyticNearOne, hNoPole hAnalyticNearOne⟩

end Omega.Conclusion
