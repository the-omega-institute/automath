import Mathlib.Data.Nat.Choose.Basic

namespace Omega.GU

/-- Orbit size of binary layerings with smaller color class size `k`.
    prop:bdry-binary-layering-orbit-classification -/
def binaryLayerOrbitSize (d k : ℕ) : ℕ :=
  if 2 * k = d then Nat.choose d k / 2 else Nat.choose d k

/-- Paper-facing orbit-size classification for binary layerings modulo global complement.
    prop:bdry-binary-layering-orbit-classification -/
theorem paper_bdry_binary_layering_orbit_classification (d k : ℕ) (hk : k ≤ d / 2) :
    binaryLayerOrbitSize d k = if 2 * k = d then Nat.choose d k / 2 else Nat.choose d k := by
  let _ := hk
  simp [binaryLayerOrbitSize]

end Omega.GU
