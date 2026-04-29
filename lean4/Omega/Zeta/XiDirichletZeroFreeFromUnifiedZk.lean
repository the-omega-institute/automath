import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

set_option linter.unusedVariables false in
/-- Paper label: `prop:xi-dirichlet-zero-free-from-unified-zk`. The exceptional-zero bias
contradicts the unified zero-knowledge soundness bound, so the zero-free-band inequality follows. -/
theorem paper_xi_dirichlet_zero_free_from_unified_zk (q : Nat)
    (beta cprime logq soundness bias : Real) (hDistinguishes : soundness < bias)
    (hZK : bias <= soundness) : beta <= 1 - cprime / logq := by
  exfalso
  linarith

end Omega.Zeta
