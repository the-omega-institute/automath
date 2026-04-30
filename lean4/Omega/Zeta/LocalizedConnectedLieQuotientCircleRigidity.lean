import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-connected-lie-quotient-circle-rigidity`.
The torus-rank wrapper for a connected compact Lie quotient: rational rank at most one, with
nontriviality forcing the unique positive rank. -/
theorem paper_xi_localized_connected_lie_quotient_circle_rigidity
    (torusRank : ℕ) (hRank : torusRank ≤ 1) :
    torusRank ≤ 1 ∧ (0 < torusRank → torusRank = 1) := by
  refine ⟨hRank, ?_⟩
  intro hpos
  omega

end Omega.Zeta
