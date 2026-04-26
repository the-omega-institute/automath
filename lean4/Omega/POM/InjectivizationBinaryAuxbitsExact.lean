import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Omega.POM

/-- Binary auxiliary bits exactly characterize the dyadic capacity threshold.
    cor:pom-injectivization-binary-auxbits-exact -/
theorem paper_pom_injectivization_binary_auxbits_exact (D k : ℕ) (hD : 0 < D) :
    D ≤ 2 ^ k ↔ Nat.clog 2 D ≤ k := by
  cases D with
  | zero => cases hD
  | succ D =>
      exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).symm

end Omega.POM
