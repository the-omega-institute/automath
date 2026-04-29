import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Conclusion.FixedResolutionScreenCorankAuditCostLaw
import Omega.Conclusion.ScreenEntropyAuditIdentity

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-modp-fiber-entropy-audit-corank`. The fixed-resolution
screen corank package identifies the audit cost with the screen-kernel rank, so every nonempty
mod-`p` fiber has the expected cardinality `p^r` and its base-`p` entropy equals both the audit
corank and the kernel rank. -/
theorem paper_conclusion_screen_modp_fiber_entropy_audit_corank
    (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hp : 1 < p) :
    let fiberCard := p ^ fixedResolutionScreenKernelRank m n
    fiberCard = p ^ fixedResolutionScreenAuditCost m n ∧
      Nat.log p fiberCard = fixedResolutionScreenAuditCost m n ∧
      Nat.log p fiberCard = fixedResolutionScreenKernelRank m n := by
  let fiberCard : ℕ := p ^ fixedResolutionScreenKernelRank m n
  have haudit :
      fixedResolutionScreenAuditCost m n = fixedResolutionScreenKernelRank m n := by
    exact
      (paper_conclusion_fixedresolution_screen_corank_audit_cost_law
        (V := Unit) m n 0 (fun _ : Finset Unit => 0) hm hn
        (by intro s; simp) (by intro s t; simp)).1
  have hlog_kernel :
      Nat.log p fiberCard = fixedResolutionScreenKernelRank m n := by
    simp [fiberCard, Nat.log_pow, hp]
  have hidentity :=
    paper_conclusion_screen_entropy_audit_identity
      (fixedResolutionScreenKernelRank m n)
      (Nat.log p fiberCard)
      (fixedResolutionScreenAuditCost m n)
      hlog_kernel
      haudit
  have hlog_audit :
      Nat.log p fiberCard = fixedResolutionScreenAuditCost m n := by
    calc
      Nat.log p fiberCard = fixedResolutionScreenKernelRank m n := hidentity.1
      _ = fixedResolutionScreenAuditCost m n := haudit.symm
  exact ⟨by simp [haudit], hlog_audit, hidentity.1⟩

end Omega.Conclusion
