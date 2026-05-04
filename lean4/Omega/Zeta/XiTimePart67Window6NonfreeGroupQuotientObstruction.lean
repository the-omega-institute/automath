import Omega.Conclusion.Window6NotRootSystemNotFreeQuotient

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part67-window6-nonfree-group-quotient-obstruction`. -/
theorem paper_xi_time_part67_window6_nonfree_group_quotient_obstruction :
    Omega.Conclusion.full_fiber_partition_is_not_a_free_finite_group_orbit_partition ∧
      Omega.Conclusion.conclusion_window6_not_root_system_not_free_quotient_groupoid_obstruction := by
  rcases Omega.Conclusion.paper_conclusion_window6_not_root_system_not_free_quotient with
    ⟨_, _, hquotient⟩
  exact ⟨hquotient.1, hquotient⟩

end Omega.Zeta
