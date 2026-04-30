import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-localized-additive-systems-maximal-onecircle-class`. -/
theorem paper_conclusion_localized_additive_systems_maximal_onecircle_class
    (primeLedgerRecoverable oneCircleVisible finiteLocalized maximalClass : Prop)
    (hlocal : primeLedgerRecoverable ∧ oneCircleVisible) (hfinite : finiteLocalized)
    (hmax : primeLedgerRecoverable → oneCircleVisible → finiteLocalized → maximalClass) :
    primeLedgerRecoverable ∧ oneCircleVisible ∧ maximalClass := by
  exact ⟨hlocal.1, hlocal.2, hmax hlocal.1 hlocal.2 hfinite⟩

end Omega.Conclusion
