import Mathlib.Tactic
import Omega.Folding.FiberArithmetic

namespace Omega.EA.StableAddComputable

open Omega

/-- `X.stableAdd` is a total computable function (trivially well-defined in Lean).
    cor:stable-add-computable -/
theorem paper_stable_add_computable (m : ℕ) (c d : X m) :
    ∃ e : X m, e = X.stableAdd c d := ⟨X.stableAdd c d, rfl⟩

/-- `X.stableAdd` computes modular addition on stable values.
    cor:stable-add-computable -/
theorem stable_add_value_sum (m : ℕ) (c d : X m) :
    stableValue (X.stableAdd c d) =
      (stableValue c + stableValue d) % Nat.fib (m + 2) :=
  X.stableValue_stableAdd c d

end Omega.EA.StableAddComputable
