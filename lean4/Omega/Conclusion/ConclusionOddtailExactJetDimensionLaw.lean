import Mathlib.Data.Nat.Basic

namespace Omega

/-- Paper label: `thm:conclusion-oddtail-exact-jet-dimension-law`. -/
theorem paper_conclusion_oddtail_exact_jet_dimension_law (dJet : ℕ → ℕ)
    (hUpper : ∀ n, 1 ≤ n → dJet n ≤ n) (hLower : ∀ n, 1 ≤ n → n ≤ dJet n) :
    ∀ n, 1 ≤ n → dJet n = n := by
  intro n hn
  exact Nat.le_antisymm (hUpper n hn) (hLower n hn)

end Omega
