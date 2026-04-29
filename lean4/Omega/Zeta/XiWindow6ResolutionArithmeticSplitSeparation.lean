import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.FiberArithmetic
import Omega.GU.CongruenceM6IdempotentsFour

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:xi-window6-resolution-arithmetic-split-separation`. -/
theorem paper_xi_window6_resolution_arithmetic_split_separation :
    Fintype.card (ZMod 21) = 21 ∧
    Omega.GU.CongruenceM6IdempotentsFour.idem21.card = 4 ∧
    ((Finset.univ : Finset (ZMod 21)).filter
        (fun e => e * e = e ∧ e ≠ 0 ∧ e ≠ 1)).card = 2 ∧
    Fintype.card (Omega.X 6) = 21 ∧
    Omega.cBinFiberHist 6 2 = 8 ∧
    Omega.cBinFiberHist 6 3 = 4 ∧
    Omega.cBinFiberHist 6 4 = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ZMod.card]
  · exact Omega.GU.CongruenceM6IdempotentsFour.paper_congruence_m6_idempotents_four
  · native_decide
  · exact X.card_X_six
  · exact Omega.cBinFiberHist_6_2
  · exact Omega.cBinFiberHist_6_3
  · exact Omega.cBinFiberHist_6_4

end Omega.Zeta
