import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:disc2-prim8-shared-ramified-37`. The explicit odd ramified-prime sets have
intersection `{37}`. -/
theorem paper_disc2_prim8_shared_ramified_37 :
    ({37} : Finset ℕ) ∩ ({3, 37} : Finset ℕ) = ({37} : Finset ℕ) := by
  ext n
  simp

end Omega.SyncKernelWeighted
