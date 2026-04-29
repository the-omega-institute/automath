import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-bulk-curvature-modsquare-holography`. -/
theorem paper_xi_bulk_curvature_modsquare_holography
    (shapeFactor : ℝ → ℂ) (pHat nuHat : ℝ → ℂ) (normSq : ℂ → ℝ)
    (pairDiffChar : ℝ → ℝ) (hdeconv : ∀ ξ, shapeFactor ξ * pHat ξ = nuHat ξ)
    (hexpand : ∀ ξ, normSq (nuHat ξ) = pairDiffChar ξ) :
    ∀ ξ, normSq (shapeFactor ξ * pHat ξ) = pairDiffChar ξ := by
  intro ξ
  rw [hdeconv ξ, hexpand ξ]

end Omega.Zeta
