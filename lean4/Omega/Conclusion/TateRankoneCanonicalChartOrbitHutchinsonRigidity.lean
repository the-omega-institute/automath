import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-tate-rankone-canonical-chart-orbit-hutchinson-rigidity`. The
orbit-closure description and affine contraction package determine the unique nonempty compact
fixed set, so the orbit statement and the Hutchinson uniqueness conclusion are obtained
together. -/
theorem paper_conclusion_tate_rankone_canonical_chart_orbit_hutchinson_rigidity
    (orbit_closure_description affine_contraction_system unique_nonempty_compact_solution : Prop)
    (hOrbit : orbit_closure_description)
    (hContract : affine_contraction_system)
    (hUnique : orbit_closure_description → affine_contraction_system →
      unique_nonempty_compact_solution) :
    orbit_closure_description ∧ unique_nonempty_compact_solution := by
  exact ⟨hOrbit, hUnique hOrbit hContract⟩

end Omega.Conclusion
