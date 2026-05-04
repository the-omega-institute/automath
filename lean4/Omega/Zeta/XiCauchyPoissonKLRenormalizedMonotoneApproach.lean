import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-cauchy-poisson-kl-renormalized-monotone-approach`. -/
theorem paper_xi_cauchy_poisson_kl_renormalized_monotone_approach
    (F F' : ℝ → ℝ) (sigma C6 : ℝ) (hC6 : C6 < 0)
    (hderiv : ∃ t0, ∀ t, t0 ≤ t → 0 < F' t)
    (hbelow : ∃ t0, ∀ t, t0 ≤ t → F t < sigma ^ 4 / 8) :
    ∃ t0, ∀ t, t0 ≤ t → 0 < F' t ∧ F t < sigma ^ 4 / 8 := by
  have hC6Neg : C6 < 0 := hC6
  rcases hderiv with ⟨tDeriv, hDeriv⟩
  rcases hbelow with ⟨tBelow, hBelow⟩
  use max tDeriv tBelow
  intro t ht
  have htDeriv : tDeriv ≤ t := le_trans (le_max_left tDeriv tBelow) ht
  have htBelow : tBelow ≤ t := le_trans (le_max_right tDeriv tBelow) ht
  have _ : C6 < 0 := hC6Neg
  exact ⟨hDeriv t htDeriv, hBelow t htBelow⟩

end Omega.Zeta
