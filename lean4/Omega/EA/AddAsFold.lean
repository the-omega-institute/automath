import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: stable addition is folding after pointwise superposition.
    cor:add-as-fold -/
theorem paper_ea_add_as_fold_seeds {m : ℕ} (w1 w2 : Omega.Word m) :
    Omega.X.stableAdd (Omega.Fold w1) (Omega.Fold w2) =
      Omega.X.ofNat m ((Omega.weight w1 + Omega.weight w2) % Nat.fib (m + 2)) := by
  simpa using Omega.X.paper_add_as_fold w1 w2

end Omega.EA
