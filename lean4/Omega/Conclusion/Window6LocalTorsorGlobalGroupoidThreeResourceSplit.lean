import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-local-torsor-global-groupoid-three-resource-split`. -/
theorem paper_conclusion_window6_local_torsor_global_groupoid_three_resource_split :
    boundary_uplift_is_regular_Z6_torsor ∧
      full_fiber_partition_is_not_a_free_finite_group_orbit_partition ∧
      (2 : ℕ) < 21 ∧
      (21 : ℕ) < 64 := by
  rcases paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch with
    ⟨hTorsor, hNotFree⟩
  exact ⟨hTorsor, hNotFree, by omega, by omega⟩

end Omega.Conclusion
