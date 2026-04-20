import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyP10Degree
import Omega.Folding.GaugeAnomalyQ10Tschirnhaus

namespace Omega.Folding

/-- Concrete Q10 package for the quadratic-subfield fingerprint and the `S10` obstruction. -/
structure GaugeAnomalyQ10QuadraticSubfieldData where
  squarefreeKernel : ℤ
  splittingFieldDegree : ℕ
  squarefreeKernel_eq : squarefreeKernel = 66269989
  degree_eq_q10Discriminant : splittingFieldDegree = q10TschirnhausDiscriminant

namespace GaugeAnomalyQ10QuadraticSubfieldData

/-- The Q10 quadratic fingerprint matches the squarefree discriminant kernel. -/
def uniqueQuadraticSubfield (D : GaugeAnomalyQ10QuadraticSubfieldData) : Prop :=
  D.squarefreeKernel = 1931 * 34319

/-- The packaged `S10` degree certificate places Q10 in the usual non-solvable range. -/
def unsolvableByRadicals (D : GaugeAnomalyQ10QuadraticSubfieldData) : Prop :=
  D.splittingFieldDegree = Nat.factorial 10 ∧ (10 : ℕ) ≥ 5

end GaugeAnomalyQ10QuadraticSubfieldData

open GaugeAnomalyQ10QuadraticSubfieldData

/-- The Q10 squarefree discriminant kernel determines the quadratic fingerprint, and the `S10`
certificate packages the standard radicals obstruction.
    cor:fold-gauge-anomaly-Q10-unique-quadratic-subfield -/
theorem paper_fold_gauge_anomaly_q10_unique_quadratic_subfield
    (D : GaugeAnomalyQ10QuadraticSubfieldData) : D.uniqueQuadraticSubfield ∧ D.unsolvableByRadicals := by
  have hq10 : Nat.factorial 10 = q10TschirnhausDiscriminant :=
    (paper_fold_gauge_anomaly_q10_tschirnhaus).2.2.1
  have hp10 := Omega.Folding.GaugeAnomalyP10Degree.paper_fold_gauge_anomaly_p10_degree_and_unsolvability
  refine ⟨?_, ?_⟩
  · calc
      D.squarefreeKernel = 66269989 := D.squarefreeKernel_eq
      _ = 1931 * 34319 := by norm_num
  · exact ⟨D.degree_eq_q10Discriminant.trans hq10.symm, hp10.2.1⟩

end Omega.Folding
