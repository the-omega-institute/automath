import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-signature-audit`. -/
theorem paper_pom_signature_audit {Instruction Signature Fingerprint CostModel : Type*}
    (Sigma : Instruction → Signature) (fingerprint : Instruction → Fingerprint)
    (costModel : Instruction → CostModel)
    (hFingerprint : ∀ I J, Sigma I = Sigma J → fingerprint I = fingerprint J)
    (hCost : ∀ I J, Sigma I = Sigma J → costModel I = costModel J)
    {I J : Instruction} (hSigma : Sigma I = Sigma J) :
    fingerprint I = fingerprint J ∧ costModel I = costModel J := by
  exact ⟨hFingerprint I J hSigma, hCost I J hSigma⟩

end Omega.POM
