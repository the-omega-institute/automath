import Omega.Conclusion.RealInput40UVAtomCore
import Omega.Conclusion.RealInput40UVPressureSilentPhase

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-pressure-maxlaw-two-phase`. -/
theorem paper_conclusion_realinput40_pressure_maxlaw_two_phase (_u v rhoCore : ℝ)
    (hv : 0 < v) :
    let rhoFull := max (Real.sqrt v) rhoCore
    rhoFull = max (Real.sqrt v) rhoCore ∧
      (rhoCore ≤ Real.sqrt v → Real.log rhoFull = Real.log v / 2) ∧
        (Real.sqrt v ≤ rhoCore → Real.log rhoFull = Real.log rhoCore) := by
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · intro hcore
    rw [max_eq_left hcore]
    simpa using Real.log_sqrt (le_of_lt hv)
  · intro hcore
    rw [max_eq_right hcore]

end Omega.Conclusion
