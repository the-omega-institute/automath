import Mathlib.Tactic

namespace Omega.Folding

/-- Paper wrapper packaging the fixed-point and zeta-function closed forms for `Y_m`.
    cor:Ym-periodic-rigidity -/
theorem paper_Ym_periodic_rigidity (fixedPoints : ℕ → ℕ) (zetaY : ℚ → ℚ)
    (hfix : ∀ n : ℕ, 0 < n → fixedPoints n = 2 ^ n)
    (hzeta : zetaY = fun z => 1 / (1 - 2 * z)) :
    (∀ n : ℕ, 0 < n → fixedPoints n = 2 ^ n) ∧ zetaY = fun z => 1 / (1 - 2 * z) := by
  exact ⟨hfix, hzeta⟩

end Omega.Folding
