import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- After shifting by `a_q`, the mod-`2` shadow is purely periodic with period `period`. -/
def Mod2ShadowPurePeriodicAfter
    (s : ℕ → ZMod 2) (a_q period : ℕ) : Prop :=
  Function.Periodic (fun n => s (a_q + n)) period

/-- Mod-`2` specialization of the periodic-tail package: any exponent `t` with `b_q ≤ 2^t`
produces pure periodicity after the shift by `a_q`. -/
theorem paper_pom_mod2_shadow_eventual_period_bound
    (s : ℕ → ZMod 2) (a_q b_q t : ℕ)
    (hperiodicTail : ∀ k : ℕ, b_q ≤ 2 ^ k → ∀ n, s (a_q + (n + 2 ^ k)) = s (a_q + n))
    (ht : b_q ≤ 2 ^ t) :
    b_q ≤ 2 ^ t ∧ Mod2ShadowPurePeriodicAfter s a_q (2 ^ t) := by
  refine ⟨ht, ?_⟩
  intro n
  simpa [Mod2ShadowPurePeriodicAfter, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    hperiodicTail t ht n

end Omega.POM
