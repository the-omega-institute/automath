namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for exchanging thermodynamic and zero-temperature
    limits in `2026_projection_ontological_mathematics_core_tams`.
    cor:double-limit -/
theorem paper_projection_double_limit {α : Type _}
    (thermodynamicLimit zeroTemperatureLimit endpoint : α)
    (hThermo : thermodynamicLimit = endpoint)
    (hZeroTemp : zeroTemperatureLimit = endpoint) :
    thermodynamicLimit = zeroTemperatureLimit ∧
      thermodynamicLimit = endpoint ∧
      zeroTemperatureLimit = endpoint := by
  exact ⟨hThermo.trans hZeroTemp.symm, hThermo, hZeroTemp⟩

end Omega.POM
