import Omega.EA.AddressNaturality

namespace Omega.EA.StableAddNoWrapTruncation

open Omega

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for no-wrap truncation: when `a + b` stays below the Fibonacci modulus,
the address agrees with the direct `X.ofNat` representative.
    cor:emergent-arithmetic-stable-add-no-wrap-truncation -/
theorem paper_ea_stable_add_no_wrap_truncation_seeds
    (m a b : ℕ) (h : a + b < Nat.fib (m + 2)) :
    Omega.EA.AddressNaturality.addr m ((a + b : ℕ) : ℤ) = Omega.X.ofNat m (a + b) := by
  refine X.toZMod_injective ?_
  calc
    X.toZMod (Omega.EA.AddressNaturality.addr m ((a + b : ℕ) : ℤ))
        = (((a + b : ℕ) : ℤ) : ZMod (Nat.fib (m + 2))) := by
          change (X.stableValueRingEquiv m)
              ((X.stableValueRingEquiv m).symm
                ((((a + b : ℕ) : ℤ) : ZMod (Nat.fib (m + 2))))) =
            (((a + b : ℕ) : ℤ) : ZMod (Nat.fib (m + 2)))
          exact (X.stableValueRingEquiv m).apply_symm_apply _
    _ = ((a + b : ℕ) : ZMod (Nat.fib (m + 2))) := by
          simp
    _ = X.toZMod (Omega.X.ofNat m (a + b)) := by
          simp [X.toZMod, X.stableValue_ofNat_lt, h]

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_ea_stable_add_no_wrap_truncation_package
    (m a b : ℕ) (h : a + b < Nat.fib (m + 2)) :
    Omega.EA.AddressNaturality.addr m ((a + b : ℕ) : ℤ) = Omega.X.ofNat m (a + b) :=
  paper_ea_stable_add_no_wrap_truncation_seeds m a b h

end Omega.EA.StableAddNoWrapTruncation
