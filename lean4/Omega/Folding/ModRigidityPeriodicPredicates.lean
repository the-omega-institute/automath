import Mathlib.Tactic
import Omega.Folding.FiberArithmetic
import Omega.Folding.MaxFiberTwoStep

namespace Omega.Folding.ModRigidityPeriodicPredicates

open Omega

/-- If `weight ω ≡ weight ω' (mod F_{m+2})`, then `Fold ω = Fold ω'`.
    cor:fold-mod-rigidity-periodic-predicates -/
theorem fold_eq_of_weight_mod_eq {m : ℕ} (ω ω' : Word m)
    (h : weight ω % Nat.fib (m + 2) = weight ω' % Nat.fib (m + 2)) :
    Fold ω = Fold ω' := by
  apply X.eq_of_stableValue_eq
  rw [stableValue_Fold_mod, stableValue_Fold_mod]
  exact h

/-- Paper package: mod rigidity implies periodic predicates.
    cor:fold-mod-rigidity-periodic-predicates -/
theorem paper_fold_mod_rigidity_periodic_predicates {m : ℕ}
    (P : X m → Prop) (ω ω' : Word m)
    (h : weight ω % Nat.fib (m + 2) = weight ω' % Nat.fib (m + 2)) :
    P (Fold ω) ↔ P (Fold ω') := by
  rw [fold_eq_of_weight_mod_eq ω ω' h]

end Omega.Folding.ModRigidityPeriodicPredicates
