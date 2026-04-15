namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for quotient functoriality in the ETDS shadow section.
    thm:quotient-functoriality -/
theorem paper_etds_quotient_functoriality
    (logFunctoriality primitiveFunctoriality quotientClassDecomposition : Prop)
    (hLog : logFunctoriality)
    (hPrimitive : logFunctoriality → primitiveFunctoriality)
    (hClasses : primitiveFunctoriality → quotientClassDecomposition) :
    logFunctoriality ∧ primitiveFunctoriality ∧ quotientClassDecomposition := by
  have hPrimitive' : primitiveFunctoriality := hPrimitive hLog
  exact ⟨hLog, hPrimitive', hClasses hPrimitive'⟩

end Omega.Zeta
