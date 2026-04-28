import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing wrapper for the Connes-pairing-to-holonomy chain.
    thm:xi-time-index-theorem-k1-holonomy -/
theorem paper_xi_time_index_theorem_k1_holonomy
    (indexPairing holonomyPairing characteristicPairing : Prop) (hIndex : indexPairing)
    (hHolonomy : indexPairing → holonomyPairing)
    (hCharacteristic : holonomyPairing → characteristicPairing) :
    indexPairing ∧ holonomyPairing ∧ characteristicPairing := by
  exact ⟨hIndex, hHolonomy hIndex, hCharacteristic (hHolonomy hIndex)⟩

end Omega.Zeta
