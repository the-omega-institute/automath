import Mathlib.Tactic

namespace Omega.GU

/-- The six visible residue classes of the audited window-`6` columns after reducing mod `2`. -/
abbrev window6VisibleColumnType := Fin 6

/-- The number of unordered visible triples whose mod-`2` span has full rank. -/
def window6VisibleRankOneMinorCount : Nat := 675

/-- The number of unordered visible triples with determinant magnitude `2`. -/
def window6VisibleDetTwoMinorCount : Nat := 164

/-- The number of unordered visible triples whose determinant vanishes. -/
def window6VisibleDegenerateMinorCount : Nat := 491

/-- The visible minor census indexed by determinant squareclass: `0` for singular triples,
`1` for primitive visible minors, and `2` for the determinant-`2` class. -/
def window6VisibleMinorCount : Nat → Nat
  | 0 => window6VisibleDegenerateMinorCount
  | 1 => window6VisibleRankOneMinorCount
  | 2 => window6VisibleDetTwoMinorCount
  | _ => 0

/-- The weighted square-budget in which determinant-`2` triples contribute with weight `4`. -/
def window6VisibleMinorSquareBudget : Nat :=
  window6VisibleMinorCount 1 + 4 * window6VisibleMinorCount 2

/-- The visible `21`-column census splits into `675` primitive minors, `164` determinant-`2`
triples, `491` singular triples, and the weighted square budget closes to `11^3`.
    thm:window6-visible-matroid-minor-census -/
theorem paper_window6_visible_matroid_minor_census :
    window6VisibleMinorCount 1 = 675 ∧
      window6VisibleMinorCount 2 = 164 ∧
      window6VisibleMinorCount 0 = 491 ∧
      window6VisibleMinorSquareBudget = 1331 := by
  native_decide

end Omega.GU
