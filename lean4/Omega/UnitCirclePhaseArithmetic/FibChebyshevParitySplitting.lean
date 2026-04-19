import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.FibUnitCircleUpliftIdentity

namespace Omega.UnitCirclePhaseArithmetic

/-- Even-indexed Fibonacci uplift channel on the Lee--Yang coordinate. -/
noncomputable def fibParityEven (m : ℕ) (u : ℂ) : ℂ :=
  (1 + u) ^ (2 * m) * (fibPolyC (2 * m + 1)).eval (leyangJ u)

/-- Odd-indexed Fibonacci uplift channel on the Lee--Yang coordinate. -/
noncomputable def fibParityOdd (m : ℕ) (u : ℂ) : ℂ :=
  (1 + u) ^ (2 * m + 1) * (fibPolyC (2 * m + 2)).eval (leyangJ u)

/-- Even second-kind Chebyshev channel written in the unit-circle parameter. -/
noncomputable def chebyshevUEven (m : ℕ) (u : ℂ) : ℂ :=
  (u ^ (2 * m + 1) - 1) / (u - 1)

/-- Odd second-kind Chebyshev channel written in the unit-circle parameter. -/
noncomputable def chebyshevUOdd (m : ℕ) (u : ℂ) : ℂ :=
  (u ^ (2 * m + 2) - 1) / (u - 1)

/-- The parity split of the Fibonacci uplift identifies the even and odd subsequences with the
corresponding Chebyshev `U` channels, and the even subsequence satisfies the induced three-term
recurrence. -/
def FibChebyshevParitySplittingLaw (m : ℕ) : Prop :=
  ∀ u : ℂ, u ≠ 1 → u ≠ -1 →
    fibParityEven m u = chebyshevUEven m u ∧
      fibParityOdd m u = chebyshevUOdd m u ∧
      chebyshevUEven (m + 2) u =
        (1 + u ^ 2) * chebyshevUEven (m + 1) u - u ^ 2 * chebyshevUEven m u

private theorem chebyshevUEven_recurrence (m : ℕ) (u : ℂ) (hu1 : u ≠ 1) :
    chebyshevUEven (m + 2) u =
      (1 + u ^ 2) * chebyshevUEven (m + 1) u - u ^ 2 * chebyshevUEven m u := by
  unfold chebyshevUEven
  have hu_sub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  field_simp [hu_sub]
  ring

/-- Evaluating the Fibonacci uplift on the Lee--Yang coordinate and splitting into even and odd
indices recovers the parity-split Chebyshev `U` channels, with the even subsequence obeying the
induced three-term recurrence.
    thm:fib-chebyshev-parity-splitting -/
theorem paper_fib_chebyshev_parity_splitting (m : ℕ) : FibChebyshevParitySplittingLaw m := by
  intro u hu1 hum1
  refine ⟨?_, ?_, chebyshevUEven_recurrence m u hu1⟩
  · simpa [fibParityEven, chebyshevUEven] using
      paper_fib_unit_circle_uplift_identity (2 * m + 1) (by omega) u hu1 hum1
  · simpa [fibParityOdd, chebyshevUOdd] using
      paper_fib_unit_circle_uplift_identity (2 * m + 2) (by omega) u hu1 hum1

end Omega.UnitCirclePhaseArithmetic
