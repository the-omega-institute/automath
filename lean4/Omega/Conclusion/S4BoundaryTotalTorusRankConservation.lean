import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three semistable `S₄` boundary types appearing in the paper. -/
inductive S4BoundaryType
  | one
  | two
  | three
  deriving DecidableEq

/-- Main-component genus data imported from the boundary decomposition table. -/
def mainGenus : S4BoundaryType → ℕ
  | .one => 4
  | .two => 10
  | .three => 12

/-- Total torus-rank data imported from the isotypic toric-rank table. -/
def totalTorusRank : S4BoundaryType → ℕ
  | .one => 12
  | .two => 6
  | .three => 4

/-- Paper: `thm:conclusion-s4-boundary-total-torus-rank-conservation`.
For each of the three semistable `S₄` boundary types, the main-component genus and the total
torus rank add up to `16`. -/
theorem paper_conclusion_s4_boundary_total_torus_rank_conservation :
    ∀ r : S4BoundaryType, mainGenus r + totalTorusRank r = 16 := by
  intro r
  cases r <;> decide

end Omega.Conclusion
