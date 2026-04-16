import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Chapter-local template for the paper's continuum-limit criterion. It stores the four
hypotheses used by the text and an abstract compactness extractor producing a weak limit
candidate. -/
structure PhysicalSpacetimeContinuumFamily where
  Limit : Type
  convergesTo : Limit → Prop
  subadditiveControlled : Prop
  subadditiveControlledWitness : subadditiveControlled
  curvatureWeaklyCompact : Prop
  curvatureWeaklyCompactWitness : curvatureWeaklyCompact
  observerInvariant : Prop
  observerInvariantWitness : observerInvariant
  refinementCompatible : Prop
  refinementCompatibleWitness : refinementCompatible
  weakCompactness :
    subadditiveControlled →
      curvatureWeaklyCompact →
        observerInvariant → refinementCompatible → ∃ limit, convergesTo limit

/-- The continuum-limit template packages the four chapter hypotheses into a single abstract
compactness extraction, yielding a weak limit candidate.
    prop:physical-spacetime-continuum-limit-template -/
theorem paper_physical_spacetime_continuum_limit_template
    (h : PhysicalSpacetimeContinuumFamily) :
    ∃ limit, h.convergesTo limit := by
  exact
    h.weakCompactness h.subadditiveControlledWitness h.curvatureWeaklyCompactWitness
      h.observerInvariantWitness h.refinementCompatibleWitness

end Omega.PhysicalSpacetimeSkeleton
