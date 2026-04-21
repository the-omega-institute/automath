import Mathlib.Data.Set.PowersetCard
import Mathlib.Tactic

namespace Omega.SPG

/-- Paper label: `prop:conclusion-dyadic-boundary-code-central-binomial-wall`. Choosing the
equidistant shell between two words that differ in `2n` positions is equivalent to choosing the
`n` coordinates inherited from one endpoint, so the shell size is the central binomial
coefficient. -/
theorem paper_conclusion_dyadic_boundary_code_central_binomial_wall (n : ℕ) :
    Fintype.card {S : Finset (Fin (2 * n)) // S.card = n} = Nat.choose (2 * n) n := by
  rw [Fintype.card_eq_nat_card]
  change Nat.card (Set.powersetCard (Fin (2 * n)) n) = Nat.choose (2 * n) n
  calc
    Nat.card (Set.powersetCard (Fin (2 * n)) n) = Nat.choose (Nat.card (Fin (2 * n))) n := by
      exact Set.powersetCard.card (α := Fin (2 * n)) (n := n)
    _ = Nat.choose (2 * n) n := by simp

end Omega.SPG
