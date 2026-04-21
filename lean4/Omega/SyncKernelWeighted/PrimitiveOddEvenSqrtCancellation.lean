import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The two leading spectral channels: a Perron root `ρ` and a negative square-root mode. -/
def primitiveOddEvenTrace (ρ : ℝ) (n : ℕ) : ℝ :=
  ρ ^ n + (-1 : ℝ) ^ n * ρ ^ (n / 2)

/-- The part of the primitive asymptotic that survives after the odd/even split. -/
def primitiveOddEvenMainTerm (ρ : ℝ) (n : ℕ) : ℝ :=
  ρ ^ n / n - if 2 ∣ n then 0 else ρ ^ (n / 2) / n

/-- The residual square-root-scale correction coming from the even `d = 2` channel. -/
def primitiveOddEvenSecondaryTerm (ρ : ℝ) (n : ℕ) : ℝ :=
  -if 2 ∣ n then ((-1 : ℝ) ^ (n / 2) * ρ ^ (n / 4)) / n else 0

/-- The model primitive count obtained after separating the dominant odd/even pieces. -/
def primitiveOddEvenPrimitiveCount (ρ : ℝ) (n : ℕ) : ℝ :=
  primitiveOddEvenMainTerm ρ n + primitiveOddEvenSecondaryTerm ρ n

/-- The negative square-root mode survives for odd `n`, while for even `n` its top-order
contribution is canceled and only the lower `n/4` correction remains.
    thm:primitive-odd-even-sqrt-cancellation -/
theorem paper_primitive_odd_even_sqrt_cancellation (ρ : ℝ) (n : ℕ) :
    primitiveOddEvenTrace ρ n = ρ ^ n + (-1 : ℝ) ^ n * ρ ^ (n / 2) ∧
      (2 ∣ n → primitiveOddEvenPrimitiveCount ρ n =
        ρ ^ n / n - ((-1 : ℝ) ^ (n / 2) * ρ ^ (n / 4)) / n) ∧
      (¬2 ∣ n → primitiveOddEvenPrimitiveCount ρ n =
        ρ ^ n / n - ρ ^ (n / 2) / n) := by
  constructor
  · rfl
  constructor
  · intro h2
    simp [primitiveOddEvenPrimitiveCount, primitiveOddEvenMainTerm, primitiveOddEvenSecondaryTerm,
      h2]
    ring
  · intro h2
    simp [primitiveOddEvenPrimitiveCount, primitiveOddEvenMainTerm, primitiveOddEvenSecondaryTerm,
      h2]

end

end Omega.SyncKernelWeighted
