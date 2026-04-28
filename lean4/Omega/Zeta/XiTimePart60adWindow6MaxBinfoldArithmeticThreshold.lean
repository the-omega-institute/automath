import Mathlib.Tactic
import Omega.Folding.FoldBinM6FiberHist

namespace Omega.Zeta

attribute [local instance] Omega.fintypeX

/-- Paper label:
`thm:xi-time-part60ad-window6-max-binfold-arithmetic-threshold`. -/
theorem paper_xi_time_part60ad_window6_max_binfold_arithmetic_threshold :
    (∀ w : Omega.X 6,
      Omega.cBinFiberMult 6 w = 4 ↔ Omega.get w.1 5 = false ∧ Omega.stableValue w ≤ 8) ∧
    (∀ w : Omega.X 6,
      Omega.get w.1 5 = false ∧ Omega.stableValue w ≤ 8 →
        (Finset.range (2 ^ 6)).filter (fun N => Omega.cBinFold 6 N = w) =
          {Omega.stableValue w, Omega.stableValue w + Nat.fib 8,
            Omega.stableValue w + Nat.fib 9, Omega.stableValue w + Nat.fib 10}) ∧
    Omega.cBinFiberHist 6 4 = 9 := by
  refine ⟨?_, ?_, Omega.cBinFiberHist_6_4⟩
  · native_decide
  · native_decide

end Omega.Zeta
