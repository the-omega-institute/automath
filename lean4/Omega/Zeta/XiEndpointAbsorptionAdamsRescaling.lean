import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The two endpoint channels relevant for the Adams rescaling law. -/
inductive XiEndpointChannel
  | minusOne
  | plusOne
  deriving DecidableEq, Repr

/-- Endpoint absorption profile before Adams rescaling. -/
def xiEndpointAbsorptionProfile (phiMinus phiPlus : ℚ) : XiEndpointChannel → ℚ
  | .minusOne => phiMinus
  | .plusOne => phiPlus

/-- The endpoint of the original profile seen from a fixed endpoint after the Adams pullback. -/
def xiEndpointAdamsSourceChannel (m : ℕ) : XiEndpointChannel → XiEndpointChannel
  | .minusOne => if Odd m then .minusOne else .plusOne
  | .plusOne => .plusOne

/-- Under the Adams pullback, each endpoint channel contributes one copy for every branch in
`Fin m`, all with the source endpoint determined by parity. -/
def xiEndpointAbsorptionAfterAdams (m : ℕ) (phiMinus phiPlus : ℚ) :
    XiEndpointChannel → ℚ
  | endpoint =>
      ∑ _branch : Fin m,
        xiEndpointAbsorptionProfile phiMinus phiPlus (xiEndpointAdamsSourceChannel m endpoint)

/-- Paper label: `thm:xi-endpoint-absorption-adams-rescaling`. -/
theorem paper_xi_endpoint_absorption_adams_rescaling
    (m : ℕ) (_hm : 1 ≤ m) (phiMinus phiPlus : ℚ) :
    (xiEndpointAbsorptionAfterAdams m phiMinus phiPlus XiEndpointChannel.minusOne =
        if Odd m then (m : ℚ) * phiMinus else (m : ℚ) * phiPlus) ∧
      xiEndpointAbsorptionAfterAdams m phiMinus phiPlus XiEndpointChannel.plusOne =
        (m : ℚ) * phiPlus := by
  by_cases hodd : Odd m
  · constructor
    · simp [xiEndpointAbsorptionAfterAdams, xiEndpointAbsorptionProfile,
        xiEndpointAdamsSourceChannel, hodd]
    · simp [xiEndpointAbsorptionAfterAdams, xiEndpointAbsorptionProfile,
        xiEndpointAdamsSourceChannel]
  · constructor
    · simp [xiEndpointAbsorptionAfterAdams, xiEndpointAbsorptionProfile,
        xiEndpointAdamsSourceChannel, hodd]
    · simp [xiEndpointAbsorptionAfterAdams, xiEndpointAbsorptionProfile,
        xiEndpointAdamsSourceChannel]

end Omega.Zeta
