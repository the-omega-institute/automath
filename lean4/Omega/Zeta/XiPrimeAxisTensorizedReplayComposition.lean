import Mathlib.Tactic

namespace Omega.Zeta

/-- If the first replay `(pi1, r1)` and the second replay `(pi2, r2)` are both injective, then
splitting the two replay registers across the two summands of `Sum Nat Nat` preserves enough
information to recover first `pi1` and then the original source. -/
theorem paper_xi_prime_axis_tensorized_replay_composition {Omega X Y : Type*} (pi1 : Omega → X)
    (pi2 : X → Y) (r1 : Omega → Nat → Nat) (r2 : X → Nat → Nat)
    (h1 : Function.Injective fun w => (pi1 w, r1 w))
    (h2 : Function.Injective fun x => (pi2 x, r2 x)) :
    Function.Injective fun w => (pi2 (pi1 w), Sum.elim (r1 w) (r2 (pi1 w))) := by
  intro w₁ w₂ h
  have hpi2 : pi2 (pi1 w₁) = pi2 (pi1 w₂) := congrArg Prod.fst h
  have hsum :
      Sum.elim (r1 w₁) (r2 (pi1 w₁)) = Sum.elim (r1 w₂) (r2 (pi1 w₂)) := congrArg Prod.snd h
  have hr2 : r2 (pi1 w₁) = r2 (pi1 w₂) := by
    funext n
    simpa using congrFun hsum (Sum.inr n)
  have hpi1 : pi1 w₁ = pi1 w₂ := h2 <| Prod.ext hpi2 hr2
  have hr1 : r1 w₁ = r1 w₂ := by
    funext n
    simpa using congrFun hsum (Sum.inl n)
  exact h1 <| Prod.ext hpi1 hr1

end Omega.Zeta
