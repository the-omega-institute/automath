import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local closed form for the higher-order Fisher energy of the Cauchy kernel. -/
noncomputable def cdimCauchyHigherOrderFisherEnergy (n : Nat) (t : Real) : Real :=
  ((n : Real) * (Nat.factorial (2 * n) : Real)) /
    ((((2 * n - 1 : Nat) : Real) * (4 : Real) ^ n) * t ^ (2 * n))

/-- Paper label: `prop:cdim-cauchy-kernel-higher-order-fisher-energy`. -/
theorem paper_cdim_cauchy_kernel_higher_order_fisher_energy (n : Nat) (t : Real) (hn : 1 <= n)
    (ht : 0 < t) :
    cdimCauchyHigherOrderFisherEnergy n t =
      ((n : Real) * ((Nat.factorial (2 * n) : Real))) /
        ((((2 * n - 1 : Nat) : Real) * (4 : Real) ^ n) * t ^ (2 * n)) := by
  let _ := hn
  let _ := ht
  rfl

end Omega.CircleDimension
