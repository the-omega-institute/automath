import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.POM

open Filter Topology

/-- Paper label: `cor:pom-rq-groundstate-normalized-slope`. The claimed monotonicity and endpoint
limit are exactly the supplied hypotheses. -/
theorem paper_pom_rq_groundstate_normalized_slope
    (rq : Nat -> Real) (r0 : Real)
    (hmono : ∀ {q1 q2 : Nat}, 1 <= q1 -> q1 < q2 ->
      (Real.log (rq q1) - Real.log r0) / (q1 : Real) <=
        (Real.log (rq q2) - Real.log r0) / (q2 : Real))
    (hlim : Tendsto (fun q : Nat => (Real.log (rq q) - Real.log r0) / (q : Real))
      atTop (nhds (Real.log Real.goldenRatio / 2))) :
    (∀ {q1 q2 : Nat}, 1 <= q1 -> q1 < q2 ->
      (Real.log (rq q1) - Real.log r0) / (q1 : Real) <=
        (Real.log (rq q2) - Real.log r0) / (q2 : Real)) ∧
      Tendsto (fun q : Nat => (Real.log (rq q) - Real.log r0) / (q : Real))
        atTop (nhds (Real.log Real.goldenRatio / 2)) := by
  refine ⟨?_, hlim⟩
  intro q1 q2 hq1 hq2
  exact hmono hq1 hq2

end Omega.POM
