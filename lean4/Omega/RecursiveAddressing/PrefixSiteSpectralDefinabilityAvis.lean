import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- Paper label: `thm:prefix-site-spectral-definability-avis`. -/
theorem paper_prefix_site_spectral_definability_avis {Char : Type*}
    (inVisible gaugeInvariant : Char → Prop)
    (h_bad : ∀ χ, ¬ inVisible χ → ¬ gaugeInvariant χ)
    (h_good : ∀ χ, inVisible χ → gaugeInvariant χ) :
    ∀ χ, gaugeInvariant χ ↔ inVisible χ := by
  intro χ
  constructor
  · intro hgauge
    by_contra hnot_visible
    exact h_bad χ hnot_visible hgauge
  · exact h_good χ

end Omega.RecursiveAddressing
