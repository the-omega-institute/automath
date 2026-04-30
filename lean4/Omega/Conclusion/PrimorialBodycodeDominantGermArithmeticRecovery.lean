import Omega.Conclusion.PrimorialBodycodePoleResidueInversion

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-primorial-bodycode-dominant-germ-arithmetic-recovery`. -/
theorem paper_conclusion_primorial_bodycode_dominant_germ_arithmetic_recovery
    (poleResidueInversion noLeadingLogperiodic normalizedAmplitude : Prop)
    (hPole : poleResidueInversion) (hNoLog : noLeadingLogperiodic)
    (hAmp : poleResidueInversion → noLeadingLogperiodic → normalizedAmplitude) :
    poleResidueInversion ∧ normalizedAmplitude := by
  exact ⟨hPole, hAmp hPole hNoLog⟩

end Omega.Conclusion
