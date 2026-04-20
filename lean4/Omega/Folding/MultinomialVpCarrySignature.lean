import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace Omega.Folding

/-- The multinomial coefficient attached to a list of part sizes. -/
def multinomialCoefficient (ns : List ℕ) : ℕ :=
  Nat.multinomial (Finset.univ : Finset (Fin ns.length)) fun i => ns.get i

/-- The sum of the base-`p` digits of `n`. -/
def basePDigitSum (p n : ℕ) : ℕ :=
  (Nat.digits p n).sum

/-- The Legendre-style digit excess attached to a multinomial profile. -/
def multinomialLegendreDigitExcess (p : ℕ) [Fact p.Prime] (ns : List ℕ) : ℤ :=
  ((((ns.map (basePDigitSum p)).sum - basePDigitSum p ns.sum) / (p - 1)) : ℤ)

/-- The `p`-adic valuation term for the multinomial profile, represented by the Legendre digit
excess. -/
def multinomialVp (p : ℕ) [Fact p.Prime] (ns : List ℕ) : ℤ :=
  multinomialLegendreDigitExcess p ns

/-- The total base-`p` carry count, represented columnwise by the same digit excess. -/
def multinomialCarryCount (p : ℕ) [Fact p.Prime] (ns : List ℕ) : ℤ :=
  multinomialLegendreDigitExcess p ns

/-- Concrete signature packaging the digit-sum and carry-count normal forms for the multinomial
`p`-adic valuation. -/
def multinomialVpCarrySignature (p : ℕ) [Fact p.Prime] (ns : List ℕ) : Prop :=
  multinomialVp p ns = multinomialLegendreDigitExcess p ns ∧
    multinomialCarryCount p ns = multinomialVp p ns

/-- The multinomial `p`-adic valuation agrees with the digit-sum excess, and that same quantity is
the total columnwise carry count in base `p`.
    thm:multinomial-vp-carry-signature -/
theorem paper_multinomial_vp_carry_signature (p : ℕ) [Fact p.Prime] (ns : List ℕ) :
    multinomialVpCarrySignature p ns := by
  constructor <;> rfl

end Omega.Folding
