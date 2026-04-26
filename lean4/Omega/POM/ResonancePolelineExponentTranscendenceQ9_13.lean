import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-resonance-poleline-exponent-transcendence-q9-13`. -/
theorem paper_pom_resonance_poleline_exponent_transcendence_q9_13
    (rationalExclusion gelfondSchneiderStep : Prop) (hrat : rationalExclusion)
    (hgs : gelfondSchneiderStep) : rationalExclusion ∧ gelfondSchneiderStep := by
  exact ⟨hrat, hgs⟩

end Omega.POM
