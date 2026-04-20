import Mathlib.Tactic
import Omega.CircleDimension.EndpointTristateSet

namespace Omega.CircleDimension

/-- Primitive endpoint degeneration at `S = 0`: odd degrees collapse to the central value `0`,
multiples of `4` land at `2`, and the remaining even class lands at `-2`.
    prop:primitive-endpoint-tristate-degeneration -/
theorem paper_primitive_endpoint_tristate_degeneration (hatp : ℤ → ℚ) (d : ℕ) (hd : 1 ≤ d) :
    hatp (Omega.Discussion.chebyAdams d 0) =
      if d % 2 = 1 then hatp 0 else if d % 4 = 0 then hatp 2 else hatp (-2) := by
  rcases paper_endpoint_tristate_compression d hd with ⟨hodd, hzero, htwo⟩
  by_cases hodd' : d % 2 = 1
  · simp [hodd', hodd hodd']
  · by_cases hzero' : d % 4 = 0
    · simp [hodd', hzero', hzero hzero']
    · have hlt : d % 4 < 4 := Nat.mod_lt d (by decide)
      have htwo' : d % 4 = 2 := by
        omega
      simp [hodd', hzero', htwo', htwo htwo']

end Omega.CircleDimension
