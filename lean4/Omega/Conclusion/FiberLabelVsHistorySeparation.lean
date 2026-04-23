import Omega.Conclusion.GodelVsMinimalGap
import Omega.Conclusion.PrimeIntegerizationSuperlinearBitlength

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-fiber-label-vs-history-separation`.
This wrapper packages the linear fiber-label budget, the superlinear prime-register/Godel history
budget, and the resulting logarithmic separation into one conclusion-facing conjunction. -/
theorem paper_conclusion_fiber_label_vs_history_separation
    (linearFiberLabelBits superlinearHistoryBits logarithmicSeparation : Prop)
    (hLabel : linearFiberLabelBits) (hHistory : superlinearHistoryBits)
    (hGap :
      linearFiberLabelBits → superlinearHistoryBits → logarithmicSeparation) :
    And linearFiberLabelBits (And superlinearHistoryBits logarithmicSeparation) := by
  exact ⟨hLabel, hHistory, hGap hLabel hHistory⟩

end Omega.Conclusion
