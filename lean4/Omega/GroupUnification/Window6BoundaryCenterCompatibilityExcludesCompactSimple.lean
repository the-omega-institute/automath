import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Quantitative boundary/center data for the window-6 compatibility audit. The universal bound
`2 * typeDEvenCount + otherTwoTorsionFactorCount` records the total available `2`-torsion rank
after passing to finite central quotients, and the simple-case field packages the fact that a
compact connected simple factor never reaches rank `3`. -/
structure Window6BoundaryCenterCompatibilityData where
  typeDEvenCount : ℕ
  otherTwoTorsionFactorCount : ℕ
  centerTwoTorsionRank : ℕ
  compactConnectedSimple : Bool
  finiteCentralQuotientBound :
    centerTwoTorsionRank ≤ 2 * typeDEvenCount + otherTwoTorsionFactorCount
  boundaryRankThreeInjection : 3 ≤ centerTwoTorsionRank
  simpleCaseBound :
    compactConnectedSimple = true → 2 * typeDEvenCount + otherTwoTorsionFactorCount ≤ 2

namespace Window6BoundaryCenterCompatibilityData

/-- Boolean wrapper for the simple-case hypothesis. -/
def isCompactConnectedSimple (D : Window6BoundaryCenterCompatibilityData) : Prop :=
  D.compactConnectedSimple = true

end Window6BoundaryCenterCompatibilityData

open Window6BoundaryCenterCompatibilityData

/-- The boundary-required injection of `(Z/2)^3` forces the center `2`-torsion rank to be at
least `3`, hence incompatible with the universal simple-case bound. The same bound records the
quantitative inequality for all finite central quotients.
    thm:window6-boundary-center-compatibility-excludes-compact-simple -/
theorem paper_window6_boundary_center_compatibility_excludes_compact_simple
    (D : Window6BoundaryCenterCompatibilityData) :
    ¬ D.isCompactConnectedSimple ∧
      D.centerTwoTorsionRank ≤ 2 * D.typeDEvenCount + D.otherTwoTorsionFactorCount ∧
      (3 ≤ D.centerTwoTorsionRank →
        3 ≤ 2 * D.typeDEvenCount + D.otherTwoTorsionFactorCount) := by
  refine ⟨?_, D.finiteCentralQuotientBound, ?_⟩
  · intro hSimple
    have hBound2 : 2 * D.typeDEvenCount + D.otherTwoTorsionFactorCount ≤ 2 :=
      D.simpleCaseBound hSimple
    have hRankLe2 : D.centerTwoTorsionRank ≤ 2 :=
      le_trans D.finiteCentralQuotientBound hBound2
    have hRankGe3 : 3 ≤ D.centerTwoTorsionRank := D.boundaryRankThreeInjection
    omega
  · intro hRank
    exact le_trans hRank D.finiteCentralQuotientBound

end Omega.GroupUnification
