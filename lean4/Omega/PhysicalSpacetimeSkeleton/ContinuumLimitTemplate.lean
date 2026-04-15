namespace Omega.PhysicalSpacetimeSkeleton

/-- Minimal witness structure for the four continuum-limit template hypotheses together with the
weak subsequential limit extracted from them. -/
structure PhysicalSpacetimeContinuumTemplate where
  chainSubadditiveControlled : Prop
  chainSubadditiveControlled_holds : chainSubadditiveControlled
  normalizedCurvatureWeaklyCompact : Prop
  normalizedCurvatureWeaklyCompact_holds : normalizedCurvatureWeaklyCompact
  observerEquivariant : Prop
  observerEquivariant_holds : observerEquivariant
  refinementCompatible : Prop
  refinementCompatible_holds : refinementCompatible
  weakLimit : Prop → Prop → Prop
  weakLimit_exists :
    chainSubadditiveControlled →
      normalizedCurvatureWeaklyCompact →
      observerEquivariant →
      refinementCompatible →
      ∃ cone curvature : Prop, weakLimit cone curvature

/-- Paper-facing subsequence-extraction wrapper for the continuum-limit template.
    prop:physical-spacetime-continuum-limit-template -/
theorem paper_physical_spacetime_continuum_limit_template
    (T : PhysicalSpacetimeContinuumTemplate) : ∃ cone curvature : Prop, T.weakLimit cone curvature := by
  exact
    T.weakLimit_exists T.chainSubadditiveControlled_holds T.normalizedCurvatureWeaklyCompact_holds
      T.observerEquivariant_holds T.refinementCompatible_holds

end Omega.PhysicalSpacetimeSkeleton
