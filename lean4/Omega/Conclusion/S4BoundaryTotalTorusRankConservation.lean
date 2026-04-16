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

/-- The four `ℚ[S₄]`-isotypic factors tracked in the boundary tables. -/
inductive S4BoundaryFactor
  | epsilon
  | rho2
  | rho3
  | rho3prime
  deriving DecidableEq

/-- Whether the isotypic factor appears in `H^{1,0}` of the main component. -/
def appearsInMain : S4BoundaryFactor → S4BoundaryType → Prop
  | .epsilon, _ => True
  | .rho2, .one => False
  | .rho2, _ => True
  | .rho3, .three => True
  | .rho3, _ => False
  | .rho3prime, _ => True

/-- Boundary torus-rank table for the four isotypic factors. -/
def torusRank : S4BoundaryFactor → S4BoundaryType → ℕ
  | .epsilon, .one => 1
  | .epsilon, .two => 0
  | .epsilon, .three => 1
  | .rho2, .one => 2
  | .rho2, .two => 0
  | .rho2, .three => 0
  | .rho3, .one => 3
  | .rho3, .two => 3
  | .rho3, .three => 0
  | .rho3prime, .one => 6
  | .rho3prime, .two => 3
  | .rho3prime, .three => 3

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

/-- Paper: `thm:conclusion-s4-rho3prime-unique-universal-boundary-carrier`.
The `ρ₃'`-isotypic factor is the unique factor that appears in the main component and has
positive torus rank for every semistable `S₄` boundary type. -/
theorem paper_conclusion_s4_rho3prime_unique_universal_boundary_carrier :
    ∃! f : S4BoundaryFactor,
      (∀ r : S4BoundaryType, appearsInMain f r) ∧ (∀ r : S4BoundaryType, 0 < torusRank f r) := by
  refine ⟨S4BoundaryFactor.rho3prime, ?_, ?_⟩
  · constructor
    · intro r
      cases r <;> simp [appearsInMain]
    · intro r
      cases r <;> simp [torusRank]
  · intro f hf
    cases f with
    | epsilon =>
        exact False.elim ((Nat.lt_irrefl 0) (by simpa [torusRank] using hf.2 S4BoundaryType.two))
    | rho2 =>
        exact False.elim (by simpa [appearsInMain] using hf.1 S4BoundaryType.one)
    | rho3 =>
        exact False.elim (by simpa [appearsInMain] using hf.1 S4BoundaryType.one)
    | rho3prime =>
        rfl

end Omega.Conclusion
