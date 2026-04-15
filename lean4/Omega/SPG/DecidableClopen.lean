import Omega.SPG.Clopen

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: finite-resolution events are exactly unions of depth-`m` cylinders,
    and therefore clopen.
    prop:decidable-clopen -/
theorem paper_scan_projection_address_decidable_clopen_seeds
    (P : Set OmegaInfinity) (m : Nat) :
    (P ∈ prefixAlgebra m ↔ ∃ A : Set (Word m), P = fromWordSet A) ∧
      (P ∈ prefixAlgebra m → IsClopen P) := by
  refine ⟨?_, ?_⟩
  · simpa [prefixAlgebra] using prefixDetermined_iff_exists_fromWordSet P m
  · intro hP
    exact prefixDetermined_isClopen m hP

end Omega.SPG
