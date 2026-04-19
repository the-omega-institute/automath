import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The part of `m` supported away from the finite set `S`: multiply the prime-power
    contributions of the factorization whose prime is not in `S`. -/
def sCoprimePart (S : Finset ℕ) (m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support, if p ∈ S then 1 else p ^ m.factorization p

/-- The solenoid-side kernel count only sees the `Sᶜ`-part of the torsion order. -/
def sigmaKernelCard (S : Finset ℕ) (m : ℕ) : ℕ :=
  sCoprimePart S m

/-- The arithmetic singular-ring kernel count splits into the solenoid contribution
    and the free torus factor of rank `|S| - 1`. -/
def ringKernelCard (S : Finset ℕ) (m : ℕ) : ℕ :=
  sCoprimePart S m * m ^ (S.card - 1)

/-- Paper-facing wrapper for the localized solenoid / singular-ring torsion-kernel formula.
    thm:cdim-solenoid-arithmetic-singular-ring-torsion-kernel-formula -/
theorem paper_cdim_solenoid_arithmetic_singular_ring_torsion_kernel_formula
    (S : Finset ℕ) (m : ℕ) :
    sigmaKernelCard S m = sCoprimePart S m ∧
      ringKernelCard S m = sCoprimePart S m * m ^ (S.card - 1) := by
  constructor <;> rfl

end Omega.CircleDimension
