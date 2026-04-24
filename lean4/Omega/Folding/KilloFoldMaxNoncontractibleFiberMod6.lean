import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.NoncontractibleLossMod6Explicit
import Omega.Folding.CollisionZeta

namespace Omega.Folding

open Omega.Conclusion

/-- Paper label: `thm:killo-fold-max-noncontractible-fiber-mod6`.
The Fibonacci parity law `π(2) = 3` gives the parity-to-mod-`3` bridge, and the existing explicit
noncontractible-loss package supplies the even/odd formulas together with the final mod-`6`
classification. -/
theorem paper_killo_fold_max_noncontractible_fiber_mod6 :
    (∀ k : ℕ, Even (Nat.fib (k + 1)) ↔ (k + 1) % 3 = 0) ∧
      NoncontractibleLossMod6ExplicitStatement := by
  refine ⟨?_, Omega.Conclusion.paper_conclusion_noncontractible_loss_mod6_explicit⟩
  intro k
  simpa using fib_even_iff_mod3 (k + 1) (Nat.succ_le_succ (Nat.zero_le k))

end Omega.Folding
