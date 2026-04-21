import Mathlib.Tactic
import Omega.Conclusion.ThreeEndCertificateOrthogonality

namespace Omega.Conclusion

open Omega.TypedAddressBiaxialCompletion

/-- Conclusion-level data for ruling out sound-and-complete verifiers that omit one of the three
certificate ends. Each two-end verifier is represented by a concrete boolean output, and the three
omission witnesses record the failure mode left uncovered by that verifier. -/
structure ThreeEndCertificateIrreducibilityData where
  core : ThreeEndCertificateOrthogonalityData
  addrDefVerifier : Bool
  addrLinVerifier : Bool
  defLinVerifier : Bool
  addrDefRejectsFailureWitness :
    addrDefVerifier = true → ¬ core.closure.failureWitness
  addrLinRequiresLegalReadout :
    addrLinVerifier = true → core.budget.legalReadout
  defLinRequiresBoundaryCertificate :
    defLinVerifier = true → core.boundary.verifierResult = .certificate
  missingLinearWitness : ¬ core.closure.toeplitzPsdClosed
  missingDefectWitness :
    core.budget.visibleBudgetPassed ∧
      core.budget.modeBudgetPassed ∧
      ¬ core.budget.registerBudgetPassed
  missingAddressWitness :
    core.boundary.axes.radiusBlindspotClosed ∧
      core.boundary.axes.endpointHeatClosed ∧
      ¬ core.boundary.axes.addressCollisionClosed

namespace ThreeEndCertificateIrreducibilityData

def addrDefSoundComplete (D : ThreeEndCertificateIrreducibilityData) : Prop :=
  D.addrDefVerifier = true

def addrLinSoundComplete (D : ThreeEndCertificateIrreducibilityData) : Prop :=
  D.addrLinVerifier = true

def defLinSoundComplete (D : ThreeEndCertificateIrreducibilityData) : Prop :=
  D.defLinVerifier = true

end ThreeEndCertificateIrreducibilityData

open ThreeEndCertificateIrreducibilityData

/-- Paper label: `thm:conclusion-three-end-certificate-irreducibility`.
Each putative verifier that keeps only two ends is refuted by the omission witness for the third
end, using the conclusion-level orthogonality package. -/
theorem paper_conclusion_three_end_certificate_irreducibility
    (D : ThreeEndCertificateIrreducibilityData) :
    (D.addrDefSoundComplete → False) ∧
      (D.addrLinSoundComplete → False) ∧
      (D.defLinSoundComplete → False) := by
  rcases paper_conclusion_three_end_certificate_orthogonality D.core with ⟨_, hOrthogonal⟩
  rcases hOrthogonal with
    ⟨_, hBoundaryAddress, _, _, hBudgetRegister, _, hClosureFailure⟩
  refine ⟨?_, ?_⟩
  · intro hSC
    have hNoFailure := D.addrDefRejectsFailureWitness hSC
    have hFailure : D.core.closure.failureWitness :=
      hClosureFailure (Or.inr (Or.inr (Or.inr D.missingLinearWitness)))
    exact hNoFailure hFailure
  · refine ⟨?_, ?_⟩
    · intro hSC
      have hLegal := D.addrLinRequiresLegalReadout hSC
      exact (hBudgetRegister D.missingDefectWitness) hLegal
    · intro hSC
      have hCert := D.defLinRequiresBoundaryCertificate hSC
      exact (hBoundaryAddress D.missingAddressWitness) hCert

end Omega.Conclusion
