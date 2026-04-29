import Mathlib

namespace Omega.Zeta

/-- Paper label: `cor:derived-leyang-fourary-rigidity`. Evaluating the level-count identity at
`n = 1` immediately forces the address alphabet to have cardinality `4`. -/
theorem paper_derived_leyang_fourary_rigidity (D : Finset ℕ)
    (hcount : ∀ n : ℕ, 1 ≤ n → D.card ^ n = 4 ^ n) : D.card = 4 := by
  simpa using hcount 1 (by norm_num)

end Omega.Zeta
