import Omega.GU.Double12ConstraintsUniqueIntersectionM6
import Omega.GU.TerminalWindow6LocalUpliftAdmissibility
import Omega.GU.ThreefoldRigidity
import Omega.GU.Window6LocalGeometryZeroAnomalyFamilyUniqueIntersection

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing audited window-6 package: the audited resolution lists intersect only at `m = 6`,
and the local-geometry/zero-anomaly theorem then forces the three-family count and the unique
nontrivial uplift to be `N_f = 3` and `δ = 34`. Conversely, these `m = 6` values recover the
audited triple conjunction.
    cor:window6-audited-triple-conjunction-only-m6 -/
theorem paper_window6_audited_triple_conjunction_only_m6 (m Nf δ : ℕ) :
    (m ∈ boundaryTowerSum12AdmissibleResolutions ∩ order12UnitGroupAdmissibleResolutions ∧
      (δ : ℤ) ∈ terminalWindow6LocalUpliftSet ∧
      δ ≠ 0 ∧
      Nat.fib 9 ≤ 15 * Nf ∧
      15 * Nf < Nat.fib 10) ↔
    m = 6 ∧ Nf = 3 ∧ δ = 34 := by
  constructor
  · rintro ⟨hm, hGeom, hNontrivial, hTopLower, hTopUpper⟩
    have hmOnly : m ∈ (([6] : List ℕ).toFinset) := by
      simpa [paper_double_12_constraints_unique_intersection_m6] using hm
    have hm6 : m = 6 := by
      simpa using hmOnly
    have hNfδ :
        Nf = 3 ∧ δ = 34 :=
      paper_window6_local_geometry_zero_anomaly_family_unique_intersection Nf δ
        hGeom hNontrivial ⟨hTopLower, hTopUpper⟩
    rcases hNfδ with ⟨hNf, hδ⟩
    exact ⟨hm6, hNf, hδ⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, ?_, by decide, ?_, ?_⟩
    · decide
    · simp [paper_terminal_window6_local_uplift_admissibility]
    · exact Omega.GU.ThreefoldRigidity.fifteen_times_three_in_fib_range.1
    · exact Omega.GU.ThreefoldRigidity.fifteen_times_three_in_fib_range.2

end Omega.GU
