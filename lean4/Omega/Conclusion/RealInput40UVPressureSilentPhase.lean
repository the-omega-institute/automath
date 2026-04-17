import Omega.Conclusion.RealInput40UVAtomCore

namespace Omega.Conclusion

/-- In the atom-dominant region, the pressure is the rigid branch `log (sqrt v) = (log v) / 2`.
    thm:conclusion-realinput40-uv-pressure-silent-phase -/
theorem paper_conclusion_realinput40_uv_pressure_silent_phase
    (_u v rhoCore : ℝ) (hv : 0 < v) (hcore : rhoCore < Real.sqrt v) :
    Real.log (max (Real.sqrt v) rhoCore) = Real.log v / 2 := by
  rw [Omega.Conclusion.RealInput40UVAtomCore.atom_dominant_max rhoCore (Real.sqrt v) hcore]
  simpa using Real.log_sqrt (le_of_lt hv)

end Omega.Conclusion
