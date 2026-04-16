import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- Chapter-local package for the Chebotarev quotient relative-entropy chain rule. The fields
store the fine relative entropy against the uniform measure, its quotient pushforward entropy, the
average conditional fiber entropy, and the exact chain-rule identity connecting them. -/
structure ChebotarevQuotientRelativeEntropyData where
  klFineUniform : ℝ
  klCoarseUniform : ℝ
  avgFiberKlUniform : ℝ
  klFineUniform_eq :
    klFineUniform = klCoarseUniform + avgFiberKlUniform

/-- Paper-facing exact KL chain rule for the fine distribution, the quotient pushforward, and the
fiberwise conditional distributions.
    thm:kernel-chebotarev-quotient-relative-entropy-chain -/
theorem paper_kernel_chebotarev_quotient_relative_entropy_chain
    (h : ChebotarevQuotientRelativeEntropyData) :
    h.klFineUniform = h.klCoarseUniform + h.avgFiberKlUniform := by
  exact h.klFineUniform_eq

end Omega.EA
