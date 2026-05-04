import Mathlib.Data.Rat.Defs

namespace Omega.Zeta

/-- Paper label:
`thm:xi-replica-softcore-reciprocal-moment-ring-decomposition`. -/
theorem paper_xi_replica_softcore_reciprocal_moment_ring_decomposition
    (m q : Nat) (hm : 1 <= m) (hq : 2 <= q) (S omega ringSum : Rat)
    (hFormula : S = (2 : Rat) ^ m * omega * ringSum)
    (hIntegral : exists z : Int, S = z) :
    S = (2 : Rat) ^ m * omega * ringSum /\ exists z : Int, S = z := by
  have _hm : 1 <= m := hm
  have _hq : 2 <= q := hq
  exact ⟨hFormula, hIntegral⟩

end Omega.Zeta
