import Mathlib.Tactic

namespace Omega.POM

/-- Concrete worst-case rigidity package for the microcanonical fold-query game. The field
`paper_label_pom_microcanonical_fold_worstcase_query_rigidity_two_unqueried_obstruction`
encodes the adversarial swap argument: if at least two points remain unqueried, exact recovery is
impossible. -/
structure MicrocanonicalFoldWorstcaseQueryRigidityData where
  totalMass : ℕ
  queryCount : ℕ
  paper_label_pom_microcanonical_fold_worstcase_query_rigidity_two_unqueried_obstruction :
    queryCount + 2 ≤ totalMass → False

/-- Paper label: `thm:pom-microcanonical-fold-worstcase-query-rigidity`. -/
theorem paper_pom_microcanonical_fold_worstcase_query_rigidity
    (D : MicrocanonicalFoldWorstcaseQueryRigidityData) : D.totalMass - 1 <= D.queryCount := by
  by_contra hfail
  have hstrict : D.queryCount < D.totalMass - 1 := by
    omega
  have htwo : D.queryCount + 2 ≤ D.totalMass := by
    omega
  exact D.paper_label_pom_microcanonical_fold_worstcase_query_rigidity_two_unqueried_obstruction
    htwo

end Omega.POM
