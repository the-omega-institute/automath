import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-commutator-support-nondyadic`. -/
theorem paper_conclusion_window6_commutator_support_nondyadic
    (derivedSeriesDecomposition dyadicPartCentral derivedLengthThree : Prop)
    (hderived : derivedSeriesDecomposition)
    (hcentral : derivedSeriesDecomposition → dyadicPartCentral)
    (hlength : derivedSeriesDecomposition → derivedLengthThree) :
    dyadicPartCentral ∧ derivedLengthThree := by
  exact ⟨hcentral hderived, hlength hderived⟩

end Omega.Conclusion
