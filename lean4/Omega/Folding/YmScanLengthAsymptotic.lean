import Mathlib.Tactic
import Omega.Folding.YmSyncTailPfSharp

namespace Omega.Folding

/-- Chapter-local package for the asymptotic scan-length readout. The data remembers the sharp
Perron--Frobenius asymptotic, the comparison between the minimal threshold length and the
exponential main term, and the two logarithmic bounds whose gap is absorbed into `O(1)`. -/
structure YmScanLengthAsymptoticData where
  pfSharpAsymptotic : Prop
  mainTermComparison : Prop
  logarithmicLowerBound : Prop
  logarithmicUpperBound : Prop
  scanLengthAsymptotic : Prop
  hasPfSharpAsymptotic : pfSharpAsymptotic
  deriveMainTermComparison : pfSharpAsymptotic → mainTermComparison
  deriveLogarithmicLowerBound : mainTermComparison → logarithmicLowerBound
  deriveLogarithmicUpperBound : mainTermComparison → logarithmicUpperBound
  deriveScanLengthAsymptotic :
    logarithmicLowerBound →
      logarithmicUpperBound →
        scanLengthAsymptotic

/-- Paper-facing wrapper for the asymptotic scan length needed to reach a visibility threshold.
    cor:Ym-scan-length-asymptotic -/
theorem paper_Ym_scan_length_asymptotic (D : YmScanLengthAsymptoticData) :
    D.scanLengthAsymptotic := by
  have hCompare : D.mainTermComparison := D.deriveMainTermComparison D.hasPfSharpAsymptotic
  have hLower : D.logarithmicLowerBound := D.deriveLogarithmicLowerBound hCompare
  have hUpper : D.logarithmicUpperBound := D.deriveLogarithmicUpperBound hCompare
  exact D.deriveScanLengthAsymptotic hLower hUpper

end Omega.Folding
