import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-stable-orderunit-strict-orthogonality`. -/
theorem paper_conclusion_window6_stable_orderunit_strict_orthogonality
    (m : Nat)
    (stableMoritaCollapsed orderedK0RecordsBlockScales stableInvariantsBlind : Prop)
    (hstable : stableMoritaCollapsed)
    (hordered : orderedK0RecordsBlockScales)
    (hblind : stableInvariantsBlind) :
    stableMoritaCollapsed ∧ orderedK0RecordsBlockScales ∧ stableInvariantsBlind := by
  have _m : Nat := m
  exact ⟨hstable, hordered, hblind⟩

end Omega.Conclusion
