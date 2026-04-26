import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-minimal-exact-replay-symmetry-breaking`. -/
theorem paper_conclusion_window6_minimal_exact_replay_symmetry_breaking
    (ExactReplay BoundaryEquivariant FourValueBoundaryCompanion : Prop)
    (hexact_to_companion : ExactReplay → BoundaryEquivariant → FourValueBoundaryCompanion)
    (hno_companion : ¬ FourValueBoundaryCompanion) : ExactReplay → ¬ BoundaryEquivariant := by
  intro hexact hboundary
  exact hno_companion (hexact_to_companion hexact hboundary)

end Omega.Conclusion
