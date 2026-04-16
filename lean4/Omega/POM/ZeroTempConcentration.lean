namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the zero-temperature concentration theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:zero-temp-concentration -/
theorem paper_projection_zero_temp_concentration
    (maxFiberAsymptotics upperTailVanishing lowerTailVanishing concentration : Prop)
    (hUpper : maxFiberAsymptotics → upperTailVanishing)
    (hLower : maxFiberAsymptotics → lowerTailVanishing)
    (hConcentration : upperTailVanishing → lowerTailVanishing → concentration) :
    maxFiberAsymptotics →
      upperTailVanishing ∧ lowerTailVanishing ∧ concentration := by
  intro hMaxFiber
  have hUpperTail : upperTailVanishing := hUpper hMaxFiber
  have hLowerTail : lowerTailVanishing := hLower hMaxFiber
  exact ⟨hUpperTail, hLowerTail, hConcentration hUpperTail hLowerTail⟩

end Omega.POM
