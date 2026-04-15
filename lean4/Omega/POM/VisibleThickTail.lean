import Omega.POM.ThickFiberEnvelope

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the visible-tail envelope corollary in
    `2026_projection_ontological_mathematics_core_tams`.
    cor:visible-thick-tail -/
theorem paper_projection_visible_thick_tail
    (allQPressureEnvelope visibleTailUpperBound supercriticalTailExtinction
      subcriticalTailPersistence : Prop)
    (hUpper : allQPressureEnvelope → visibleTailUpperBound)
    (hExtinct : visibleTailUpperBound → supercriticalTailExtinction)
    (hPersist : visibleTailUpperBound → subcriticalTailPersistence) :
    allQPressureEnvelope →
      visibleTailUpperBound ∧ supercriticalTailExtinction ∧ subcriticalTailPersistence := by
  intro hEnvelope
  exact
    paper_projection_thick_fiber_envelope
      allQPressureEnvelope visibleTailUpperBound
      supercriticalTailExtinction subcriticalTailPersistence
      hUpper hExtinct hPersist hEnvelope

end Omega.POM
