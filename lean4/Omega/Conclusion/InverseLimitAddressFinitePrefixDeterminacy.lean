import Omega.Folding.InverseLimit

namespace Omega.Conclusion

open Omega

/-- A map out of the inverse-limit address space factors through prefix level `b` if it is obtained
from a map on the finite prefix space `X b`. -/
def factorsThroughPrefix {Y : Type*} (v : X.XInfinity → Y) (b : Nat) : Prop :=
  ∃ v_b : X b → Y, ∀ a, v a = v_b (X.prefixWord a b)

/-- Concrete prefix-factorization seed for inverse-limit observables:
any observable already defined on a fixed prefix level factors through that same level.
thm:conclusion-inverse-limit-address-finite-prefix-determinacy -/
theorem paper_conclusion_inverse_limit_address_finite_prefix_determinacy
    {Y : Type*} (b : Nat) (v_b : X b → Y) :
    ∃ n, factorsThroughPrefix (fun a : X.XInfinity => v_b (X.prefixWord a b)) n := by
  refine ⟨b, ?_⟩
  exact ⟨v_b, fun a => rfl⟩

end Omega.Conclusion
