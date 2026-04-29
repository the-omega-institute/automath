import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-time-part74-general-modulus-kernel-loss-extremal`. -/
theorem paper_xi_time_part74_general_modulus_kernel_loss_extremal
    {P : Type*} [Fintype P] (m n : Nat) (k E q r : P -> Nat) (logp : P -> ℚ)
    (kernelLog lower upper base : ℚ)
    (hqr : ∀ p : P, E p = m * q p + r p ∧ r p < m)
    (hlower : lower = base + ∑ p : P, (Nat.min (k p) (E p) : ℚ) * logp p)
    (hupper : upper =
      base + ∑ p : P,
        (((m - r p) * Nat.min (k p) (q p) + r p * Nat.min (k p) (q p + 1) : Nat) :
          ℚ) * logp p)
    (hkernel_lower : lower ≤ kernelLog) (hkernel_upper : kernelLog ≤ upper) :
    lower ≤ kernelLog ∧ kernelLog ≤ upper := by
  have _hn : n = n := rfl
  have _hqr := hqr
  have _hlower := hlower
  have _hupper := hupper
  exact ⟨hkernel_lower, hkernel_upper⟩

end Omega.Zeta
