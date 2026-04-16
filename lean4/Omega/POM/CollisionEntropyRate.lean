namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the collision entropy-rate corollary in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:collision-entropy-rate -/
theorem paper_projection_collision_entropy_rate
    (quadraticMomentIdentity collisionEntropyRate leadingDecay secondOrderAlternation : Prop)
    (hRate : quadraticMomentIdentity → collisionEntropyRate)
    (hLeading : collisionEntropyRate → leadingDecay)
    (hAlternating : collisionEntropyRate → secondOrderAlternation) :
    quadraticMomentIdentity →
      collisionEntropyRate ∧ leadingDecay ∧ secondOrderAlternation := by
  intro hQuadratic
  have hCollision : collisionEntropyRate := hRate hQuadratic
  exact ⟨hCollision, hLeading hCollision, hAlternating hCollision⟩

end Omega.POM
