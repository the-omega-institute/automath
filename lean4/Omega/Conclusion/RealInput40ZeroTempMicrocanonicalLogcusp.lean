namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-zero-temp-microcanonical-logcusp`. -/
theorem paper_conclusion_realinput40_zero_temp_microcanonical_logcusp
    (pressureExpansion stationaryInversion uniqueMinimizer thetaAsymptotic hAsymptotic : Prop)
    (hstat : pressureExpansion → stationaryInversion)
    (huniq : stationaryInversion → uniqueMinimizer)
    (htheta : stationaryInversion → thetaAsymptotic)
    (hh : stationaryInversion → hAsymptotic)
    (hP : pressureExpansion) :
    uniqueMinimizer ∧ thetaAsymptotic ∧ hAsymptotic := by
  have hstationary : stationaryInversion := hstat hP
  exact ⟨huniq hstationary, htheta hstationary, hh hstationary⟩

end Omega.Conclusion
