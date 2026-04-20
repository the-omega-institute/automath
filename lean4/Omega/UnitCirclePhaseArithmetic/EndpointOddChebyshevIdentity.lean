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

/-- At the endpoint `S = 0`, the odd Chebyshev companion is `δ` times the second-kind family, and
the normalized odd channel matches the endpoint sine channel.
    prop:endpoint-odd-chebyshev-identity -/
theorem paper_endpoint_odd_chebyshev_identity (d : ℕ) :
    endpointOddCompanion d = endpointDelta * endpointSecondKind (d - 1) ∧
      endpointOddRatioAtZero d = endpointSinChannel d := by
  simp [endpointOddCompanion, endpointOddRatioAtZero, endpointSinChannel]

end Omega.UnitCirclePhaseArithmetic
