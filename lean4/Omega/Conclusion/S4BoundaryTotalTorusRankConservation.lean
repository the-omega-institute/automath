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

/-- Paper-facing rank classification corollary: the total torus rank determines the
    semistable `S₄` boundary type.
    cor:conclusion-s4-boundary-type-by-total-toric-rank -/
theorem paper_conclusion_s4_boundary_type_by_total_toric_rank :
    ∀ r : S4BoundaryType,
      (r = S4BoundaryType.one ↔ totalTorusRank r = 12) ∧
        (r = S4BoundaryType.two ↔ totalTorusRank r = 6) ∧
          (r = S4BoundaryType.three ↔ totalTorusRank r = 4) := by
  intro r
  cases r <;> simp [totalTorusRank]

end Omega.Conclusion
