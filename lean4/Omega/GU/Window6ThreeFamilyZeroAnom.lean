import Omega.Conclusion.CompleteStrictificationDualCriterion
import Omega.Conclusion.Window6BoundaryQuotientCyclicCardinality
import Omega.GU.Window6LocalGeometryZeroAnomalyFamilyUniqueIntersection

namespace Omega.GU

open Omega.Conclusion

/-- Paper-facing window-6 zero-anomaly package: the strict zero-visible-anomaly certificate on the
three boundary channels is compatible with the audited window-6 boundary count, and the existing
local-geometry/zero-anomaly rigidity theorem forces any nontrivial realizable family count to
equal that rigid boundary cardinality.
    cor:window6-three-family-zero-anom -/
def window6ThreeFamilyZeroAnom : Prop :=
  zeroVisibleAnomaly (fun _ : Fin ((21 : ℕ) - 18) => 0) ∧
    ((21 : ℕ) - 18 = 3) ∧
    ∀ Nf δ : ℕ,
      (δ : ℤ) ∈ terminalWindow6LocalUpliftSet →
      δ ≠ 0 →
      (Nat.fib 9 ≤ 15 * Nf ∧ 15 * Nf < Nat.fib 10) →
      Nf = ((21 : ℕ) - 18)

theorem paper_window6_three_family_zero_anom : window6ThreeFamilyZeroAnom := by
  refine ⟨?_, Omega.Conclusion.Window6BoundaryQuotientCyclicCardinality.boundary_set_cardinality, ?_⟩
  · simp [zeroVisibleAnomaly]
  · intro Nf δ hGeom hNontrivial hTop
    rcases
        paper_window6_local_geometry_zero_anomaly_family_unique_intersection Nf δ hGeom hNontrivial
          hTop with
      ⟨hNf, _⟩
    rw [Omega.Conclusion.Window6BoundaryQuotientCyclicCardinality.boundary_set_cardinality]
    exact hNf

end Omega.GU
