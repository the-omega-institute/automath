import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Omega.Conclusion.BoundaryCycleRankExternalInfoLowerBound
import Omega.Conclusion.CycleRankSaturation

open Filter Topology

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing conclusion: the exact equality `Qmin = r` and the cycle-rank saturation lemma
identify the asymptotic audit complexity with the boundary area.
    cor:conclusion-boundary-audit-complexity-area-equivalence -/
theorem paper_conclusion_boundary_audit_complexity_area_equivalence
    (Qmin A r X c : ℕ → ℝ) (hA_pos : ∀ n, 0 < A n) (hQ : ∀ n, Qmin n = r n)
    (hrank : ∀ n, r n = A n - X n + c n) (hc_bound : ∀ n, 0 ≤ c n ∧ c n ≤ X n)
    (hX_nonneg : ∀ n, 0 ≤ X n)
    (hXA : Tendsto (fun n => X n / A n) Filter.atTop (nhds 0)) :
    Tendsto (fun n => Qmin n / A n) Filter.atTop (nhds 1) := by
  have hratio :
      Tendsto (fun n => r n / A n) Filter.atTop (nhds 1) :=
    Omega.Conclusion.CycleRankSaturation.paper_conclusion_boundary_cycle_rank_saturation
      r A X c hA_pos hrank hc_bound hX_nonneg hXA
  have hfun : (fun n => Qmin n / A n) = fun n => r n / A n := by
    funext n
    rw [hQ n]
  simpa [hfun] using hratio

end Omega.Conclusion
