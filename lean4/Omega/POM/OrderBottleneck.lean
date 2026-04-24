import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper label: `cor:pom-order-bottleneck`. Once `g` leaves the fold-invariant subalgebra `Bm`,
the structural gate forces either a higher-resolution statistic or an order projection. -/
theorem paper_pom_order_bottleneck {alpha : Type*} (Bm : Set (alpha -> Real)) (g : alpha -> Real)
    (needsHigherResolution needsOrderProjection : Prop) (hnot : g ∉ Bm)
    (hGate : g ∉ Bm -> needsHigherResolution ∨ needsOrderProjection) :
    needsHigherResolution ∨ needsOrderProjection := by
  exact hGate hnot

end Omega.POM
