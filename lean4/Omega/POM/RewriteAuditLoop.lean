import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `prop:pom-rewrite-audit-loop`. -/
theorem paper_pom_rewrite_audit_loop
    {Instruction Signature : Type}
    (Rewrite : Instruction → Instruction → Prop)
    (Sigma : Instruction → Signature)
    (fingerprintDepth : ℝ → ℝ → ℝ → ℝ)
    (lambda1 Lambda epsilon mixingDepth : ℝ)
    (I J : Instruction)
    (hcert : Rewrite I J)
    (hsig : ∀ {A B}, Rewrite A B → Sigma A = Sigma B)
    (hcost : mixingDepth = fingerprintDepth lambda1 Lambda epsilon) :
    Sigma I = Sigma J ∧ mixingDepth = fingerprintDepth lambda1 Lambda epsilon := by
  exact ⟨hsig hcert, hcost⟩

end Omega.POM
