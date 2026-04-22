import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing exact exponent wrapper: once the matching upper and lower asymptotic bounds meet,
the microcanonical query-distortion success exponent is exactly their common value.
    thm:pom-microcanonical-query-distortion-strong-converse-plane -/
theorem paper_pom_microcanonical_query_distortion_strong_converse_plane
    (beta bitDensity rate successExponent : Real) (hBeta0 : 0 <= beta) (hBeta1 : beta < 1)
    (hBits : 0 <= bitDensity)
    (hUpper : successExponent <= min 0 (bitDensity * Real.log 2 - (1 - beta) * rate))
    (hLower : min 0 (bitDensity * Real.log 2 - (1 - beta) * rate) <= successExponent) :
    successExponent = min 0 (bitDensity * Real.log 2 - (1 - beta) * rate) := by
  have _ := hBeta0
  have _ := hBeta1
  have _ := hBits
  linarith

end Omega.POM
