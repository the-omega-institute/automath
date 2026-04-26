import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch

namespace Omega.Conclusion

/-- A global free extension of the boundary `Z/6Z` torsor would force the full window-`6` fiber
partition to be a free finite-group orbit partition, hence to have a common orbit size `m` with
`21 * m = 64`. -/
def conclusion_window6_boundary_z6_no_global_free_extension_global_free_extension : Prop :=
  boundary_uplift_is_regular_Z6_torsor ∧ ∃ m : ℕ, 21 * m = 64

/-- Paper label: `cor:conclusion-window6-boundary-z6-no-global-free-extension`. The local
boundary torsor exists, but the ambient `64`-state window-`6` fiber partition cannot be the orbit
partition of any free finite-group action. -/
theorem paper_conclusion_window6_boundary_z6_no_global_free_extension :
    ¬ conclusion_window6_boundary_z6_no_global_free_extension_global_free_extension := by
  intro hExtension
  rcases hExtension with ⟨_, hm⟩
  rcases paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch with ⟨_, hMismatch⟩
  exact hMismatch.2.2.2 hm

end Omega.Conclusion
