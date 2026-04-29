import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-horizon-forced-geometric-tail`. -/
theorem paper_xi_horizon_forced_geometric_tail (R wρ : ℂ) (c h : ℕ → ℂ)
    (hwρ : wρ ≠ 0)
    (hcoeff : ∀ n, 1 ≤ n → 2 * c n = -R / wρ ^ (n + 1) + 2 * h n) :
    ∀ n, 1 ≤ n → c n = -R / (2 * wρ ^ (n + 1)) + h n := by
  intro n hn
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hp : wρ ^ (n + 1) ≠ 0 := pow_ne_zero _ hwρ
  have hcn := hcoeff n hn
  calc
    c n = (2 * c n) / 2 := by field_simp [htwo]
    _ = (-R / wρ ^ (n + 1) + 2 * h n) / 2 := by rw [hcn]
    _ = -R / (2 * wρ ^ (n + 1)) + h n := by
      field_simp [htwo, hp]

end Omega.Zeta
