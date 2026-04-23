import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-coherence-time-lower-bound-M-1overd`. If fewer than `M` length-`t`
readout classes are available, no encoding into `Fin p` can separate `M` instances injectively. -/
theorem paper_cdim_coherence_time_lower_bound_m_1overd (M C d t p : ℕ)
    (hBound : p ≤ C * t ^ d) (hSmall : p < M) : ¬ ∃ f : Fin M → Fin p, Function.Injective f := by
  let _ := hBound
  intro hInj
  rcases hInj with ⟨f, hf⟩
  have hCard : M ≤ p := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact Nat.not_le_of_lt hSmall hCard

end Omega.CircleDimension
