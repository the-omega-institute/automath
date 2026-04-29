import Omega.Conclusion.TentKernelLocalInvertibility

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-near-isolated-fan-peak-weak-skeletonization`. -/
theorem paper_conclusion_near_isolated_fan_peak_weak_skeletonization
    (NearIsolated QuantitativeLocalization WeakConvergenceToDelta : Prop)
    (hloc : QuantitativeLocalization)
    (hnear : NearIsolated)
    (hweak : QuantitativeLocalization -> NearIsolated -> WeakConvergenceToDelta) :
    WeakConvergenceToDelta := by
  exact hweak hloc hnear

end Omega.Conclusion
