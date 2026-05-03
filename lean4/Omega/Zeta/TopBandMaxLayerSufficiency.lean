import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9wa-top-band-max-layer-sufficiency`. -/
theorem paper_xi_time_part9wa_top_band_max_layer_sufficiency {N K M T C : ℕ → ℝ} (m0 : ℕ)
    (hN : ∀ m, m0 ≤ m → N m = K m)
    (hC : ∀ m, m0 ≤ m → C m = (2 : ℝ) ^ m - K m * (M m - T m)) :
    ∀ m, m0 ≤ m → N m = K m ∧ C m = (2 : ℝ) ^ m - K m * (M m - T m) := by
  intro m hm
  exact ⟨hN m hm, hC m hm⟩

end Omega.Zeta
