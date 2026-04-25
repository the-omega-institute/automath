import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-faithful-detector-component-lower-bound`. -/
theorem paper_conclusion_window6_boundary_faithful_detector_component_lower_bound
    {P6 PgeoQuot pi0H : Type*} [Fintype P6] [Fintype PgeoQuot] [Fintype pi0H]
    (hP6 : Fintype.card P6 = 8) (hquot : Fintype.card PgeoQuot = 4)
    (hfull : P6 ↪ pi0H) (hgeo : PgeoQuot ↪ pi0H) :
    8 ≤ Fintype.card pi0H ∧ 4 ≤ Fintype.card pi0H := by
  constructor
  · rw [← hP6]
    exact Fintype.card_le_of_embedding hfull
  · rw [← hquot]
    exact Fintype.card_le_of_embedding hgeo

end Omega.Conclusion
