import Mathlib.Tactic
import Omega.Folding.MomentBounds

namespace Omega

/-- Paper label: `cor:pom-crossq-logconvex-chain`. -/
theorem paper_pom_crossq_logconvex_chain (q r m : ℕ) (hr : r ≤ q) :
    Omega.momentSum q m ^ 2 ≤ Omega.momentSum (q - r) m * Omega.momentSum (q + r) m := by
  exact momentSum_log_convex_gap q r m hr

end Omega
