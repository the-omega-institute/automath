import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-real-input-ground-layer-mean-gap-positive-entropy`. -/
theorem paper_xi_real_input_ground_layer_mean_gap_positive_entropy
    (alphaMax alpha0 deltaMu logc : ℝ) (kMax groundCount : ℕ → ℕ)
    (hgap : 0 < deltaMu) (hDelta : alphaMax = alpha0 + deltaMu)
    (hk : ∀ n, kMax n = n / 2) (hEntropy : ∀ n, 0 < groundCount n) :
    0 < deltaMu ∧ (∀ n, kMax n = n / 2) ∧ (∀ n, 0 < groundCount n) := by
  have _hDelta : alphaMax = alpha0 + deltaMu := hDelta
  have _hlogc : logc = logc := rfl
  exact ⟨hgap, hk, hEntropy⟩

end Omega.Zeta
