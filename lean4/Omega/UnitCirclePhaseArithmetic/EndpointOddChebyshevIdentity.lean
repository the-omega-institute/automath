import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Endpoint value of the odd Chebyshev companion channel. -/
def endpointDelta : ℤ :=
  2

/-- The second-kind Chebyshev family specialized at the endpoint `S = 0`. -/
def endpointSecondKind : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | n + 2 => -endpointSecondKind n

/-- The odd companion is the endpoint delta times the specialized second-kind family. -/
def endpointOddCompanion (d : ℕ) : ℤ :=
  endpointDelta * endpointSecondKind (d - 1)

/-- The endpoint ratio obtained after dividing out the common `δ`-factor. -/
def endpointOddRatioAtZero (d : ℕ) : ℤ :=
  endpointSecondKind (d - 1)

/-- The endpoint sine channel is represented by the same four-step recursion. -/
def endpointSinChannel (d : ℕ) : ℤ :=
  endpointSecondKind (d - 1)

/-- Quarter-turn sign `sin(m π / 2)` recorded through the endpoint second-kind recurrence. -/
def endpointQuarterTurnSign (m : ℕ) : ℤ :=
  endpointSecondKind (m - 1)

/-- The derivative `C_m'(0)` of `C_m(S) = 2 T_m(S / 2)` at the endpoint `S = 0`. -/
def endpointChebyshevDerivative (m : ℕ) : ℤ :=
  (m : ℤ) * endpointQuarterTurnSign m

/-- The endpoint value `C_m(0)` of `C_m(S) = 2 T_m(S / 2)`. -/
def endpointChebyshevValue (m : ℕ) : ℤ :=
  endpointDelta * endpointSecondKind m

private theorem endpointSecondKind_odd (k : ℕ) :
    endpointSecondKind (2 * k + 1) = 0 := by
  induction k with
  | zero =>
      simp [endpointSecondKind]
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, endpointSecondKind]
      simp [ih]

private theorem endpointSecondKind_even_natAbs (k : ℕ) :
    Int.natAbs (endpointSecondKind (2 * k)) = 1 := by
  induction k with
  | zero =>
      simp [endpointSecondKind]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, endpointSecondKind]
      simp [ih]

/-- At the endpoint `S = 0`, the odd Chebyshev companion is `δ` times the second-kind family, and
the normalized odd channel matches the endpoint sine channel.
    prop:endpoint-odd-chebyshev-identity -/
theorem paper_endpoint_odd_chebyshev_identity (d : ℕ) :
    endpointOddCompanion d = endpointDelta * endpointSecondKind (d - 1) ∧
      endpointOddRatioAtZero d = endpointSinChannel d := by
  simp [endpointOddCompanion, endpointOddRatioAtZero, endpointSinChannel]

/-- Paper label: `prop:chebyshev-endpoint-derivative-splitting`.
The endpoint derivative is `m sin(m π / 2)`, so the even channel vanishes to first order while the
odd channel has zero endpoint value and derivative of absolute value `m`. -/
theorem paper_chebyshev_endpoint_derivative_splitting (m : ℕ) :
    endpointChebyshevDerivative m = m * endpointQuarterTurnSign m ∧
      (Even m → endpointChebyshevDerivative m = 0) ∧
      (¬ Even m →
        endpointChebyshevValue m = 0 ∧ Int.natAbs (endpointChebyshevDerivative m) = m) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hm
    rcases hm with ⟨k, rfl⟩
    cases k with
    | zero =>
        simp [endpointChebyshevDerivative, endpointQuarterTurnSign]
    | succ k =>
        have hsub : k + 1 + (k + 1) - 1 = 2 * k + 1 := by omega
        rw [endpointChebyshevDerivative, endpointQuarterTurnSign, hsub, endpointSecondKind_odd]
        simp
  · intro hm
    rcases Nat.even_or_odd m with hEven | hOdd
    · exact (hm hEven).elim
    · rcases hOdd with ⟨k, rfl⟩
      refine ⟨?_, ?_⟩
      · simp [endpointChebyshevValue, endpointSecondKind_odd]
      · have hsub : 2 * k + 1 - 1 = 2 * k := by omega
        rw [endpointChebyshevDerivative, endpointQuarterTurnSign, hsub, Int.natAbs_mul,
          endpointSecondKind_even_natAbs]
        simpa [Nat.cast_add, Nat.cast_mul] using Int.natAbs_natCast (2 * k + 1)

end Omega.UnitCirclePhaseArithmetic
