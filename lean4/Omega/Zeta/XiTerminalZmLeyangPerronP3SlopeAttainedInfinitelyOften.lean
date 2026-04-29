import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-leyang-perron-p3-slope-attained-infinitely-often`. -/
theorem paper_xi_terminal_zm_leyang_perron_p3_slope_attained_infinitely_often
    (b : ℕ → ZMod 3) (valuationSharp : ℕ → Prop)
    (hsharp : ∀ n, b n ≠ 0 ↔ valuationSharp n)
    (hinf : Set.Infinite {n : ℕ | b n ≠ 0}) :
    Set.Infinite {n : ℕ | valuationSharp n} := by
  have hset : {n : ℕ | valuationSharp n} = {n : ℕ | b n ≠ 0} := by
    ext n
    exact (hsharp n).symm
  simpa [hset] using hinf

end Omega.Zeta
