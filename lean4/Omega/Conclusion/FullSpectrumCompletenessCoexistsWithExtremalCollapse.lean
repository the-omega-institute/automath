import Omega.Conclusion.CapacityOrderedSpectrumInfoNCEEquivalence
import Omega.Conclusion.FreezingExtremalSkeletonTwoCoordinates

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-full-spectrum-completeness-coexists-with-extremal-collapse`.  Finite
tomography and extremal-skeleton collapse coexist after transporting the two components
through the supplied coexistence implication. -/
theorem paper_conclusion_full_spectrum_completeness_coexists_with_extremal_collapse
    (finiteTomography extremalCollapse coexistence : Prop) (hfinite : finiteTomography)
    (hcollapse : extremalCollapse)
    (hcoexist : finiteTomography → extremalCollapse → coexistence) :
    finiteTomography ∧ extremalCollapse ∧ coexistence := by
  exact ⟨hfinite, hcollapse, hcoexist hfinite hcollapse⟩

end Omega.Conclusion
