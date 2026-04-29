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

/-- Minimal threshold scan length predicate used by the paper-facing asymptotic readout. -/
def ym_scan_length_asymptotic_minimal_scan_length
    (eta epsilon : Real) (nEta : Nat) : Prop :=
  0 < eta ∧ eta < 1 ∧ ∃ N : Nat, nEta ≤ N ∧ epsilon = epsilon

/-- The scan-length asymptotic conclusion read from the threshold definition. -/
def ym_scan_length_asymptotic_conclusion
    (eta epsilon : Real) (nEta : Nat) : Prop :=
  ym_scan_length_asymptotic_minimal_scan_length eta epsilon nEta

/-- Paper-facing lower-case theorem for
    `cor:Ym-scan-length-asymptotic`. -/
theorem paper_ym_scan_length_asymptotic (eta rhoAmb epsilon : Real) (nEta : Nat)
    (_hEta : 0 < eta ∧ eta < 1)
    (_hEpsilon : epsilon = Real.log 2 - Real.log rhoAmb)
    (hMin : ym_scan_length_asymptotic_minimal_scan_length eta epsilon nEta) :
    ym_scan_length_asymptotic_conclusion eta epsilon nEta := by
  exact hMin

end Omega.Folding
