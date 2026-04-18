import Mathlib.Tactic
import Omega.Discussion.ChebyshevAdams

namespace Omega.CircleDimension

open Omega.Discussion

/-- The endpoint four-channel sign pattern, written as the nontrivial Dirichlet character modulo
`4` on positive integers. -/
def endpointChi4 (d : Nat) : ℤ :=
  if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1

private theorem chebyAdams_at_zero_add_four_mul (r q : Nat) :
    chebyAdams (r + 4 * q) 0 = chebyAdams r 0 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [show r + 4 * (q + 1) = (r + 4 * q) + 4 by ring, chebyAdams_at_zero_period4, ih]

/-- The endpoint sign readout is exactly the mod-`4` Dirichlet character, recovered from the
period-`4` Chebyshev-Adams values at `0`.
    thm:endpoint-four-channel-chi4 -/
theorem paper_endpoint_four_channel_chi4 (d : Nat) (hd : 1 ≤ d) :
    chebyAdams (d - 1) 0 = 2 * endpointChi4 d := by
  have hcases : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    have hlt : d % 4 < 4 := Nat.mod_lt _ (by decide)
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hd' : d - 1 = 3 + 4 * ((d / 4) - 1) := by
      omega
    have heven : d % 2 = 0 := by
      omega
    rw [hd']
    simpa [endpointChi4, heven, h0] using chebyAdams_at_zero_add_four_mul 3 ((d / 4) - 1)
  · have hd' : d - 1 = 0 + 4 * (d / 4) := by
      omega
    have hodd : d % 2 = 1 := by
      omega
    rw [hd']
    simpa [endpointChi4, hodd, h1] using chebyAdams_at_zero_add_four_mul 0 (d / 4)
  · have hd' : d - 1 = 1 + 4 * (d / 4) := by
      omega
    have heven : d % 2 = 0 := by
      omega
    rw [hd']
    simpa [endpointChi4, heven, h2] using chebyAdams_at_zero_add_four_mul 1 (d / 4)
  · have hd' : d - 1 = 2 + 4 * (d / 4) := by
      omega
    have hodd : d % 2 = 1 := by
      omega
    rw [hd']
    simpa [endpointChi4, hodd, h3] using chebyAdams_at_zero_add_four_mul 2 (d / 4)

end Omega.CircleDimension
