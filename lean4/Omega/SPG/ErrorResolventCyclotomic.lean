import Omega.SPG.FirstEntryEscapeRate

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the supplementary resolvent/cyclotomic lift
    theorem in the scan-projection ETDS resonance section.
    thm:error-resolvent-cyclotomic -/
theorem paper_scan_projection_address_error_resolvent_cyclotomic
    (errorLift resolventFormula rationalExtension kroneckerProductFormula
      determinantLift spectrumLift poleContainment positiveRealPoleLeastModulus : Prop)
    (ρH PY PYH escapeRate ambiguityRate zH reciprocalEscapeFactor : ℝ)
    (mixing holeNonempty holeProper : Prop)
    (hρ : ρH = Real.exp (PYH - PY))
    (hEscape :
      mixing → ρH < 1 → holeNonempty → holeProper → escapeRate = -Real.log ρH)
    (hAmbiguity : ambiguityRate = escapeRate)
    (hErrorLift : errorLift)
    (hResolvent : resolventFormula)
    (hRational : rationalExtension)
    (hKronecker : kroneckerProductFormula)
    (hDet : determinantLift)
    (hSpectrum : spectrumLift)
    (hPoles : poleContainment)
    (hzH : zH = reciprocalEscapeFactor)
    (hLeastPole : positiveRealPoleLeastModulus) :
    errorLift ∧
      resolventFormula ∧
      rationalExtension ∧
      kroneckerProductFormula ∧
      determinantLift ∧
      spectrumLift ∧
      poleContainment ∧
      zH = reciprocalEscapeFactor ∧
      positiveRealPoleLeastModulus ∧
      (mixing → ρH < 1 → holeNonempty → holeProper →
        escapeRate = PY - PYH ∧ ambiguityRate = PY - PYH) := by
  have hFirstEntry :=
    paper_scan_projection_address_first_entry_escape_rate
      ρH PY PYH escapeRate ambiguityRate
      mixing holeNonempty holeProper
      hρ hEscape hAmbiguity
  exact
    ⟨hErrorLift, hResolvent, hRational, hKronecker, hDet, hSpectrum, hPoles, hzH,
      hLeastPole, hFirstEntry⟩

end Omega.SPG
