import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part61aca-primeweighted-sigma-orthogonal-independence`. -/
theorem paper_xi_time_part61aca_primeweighted_sigma_orthogonal_independence
    (AsymptoticIndependent : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop)
    (sigmaBilin : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ)
    (hGaussian :
      ∀ a b, a ≠ 0 → b ≠ 0 → (AsymptoticIndependent a b ↔ sigmaBilin a b = 0))
    (a b : Fin 2 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    AsymptoticIndependent a b ↔ sigmaBilin a b = 0 := by
  exact hGaussian a b ha hb

end Omega.Zeta
