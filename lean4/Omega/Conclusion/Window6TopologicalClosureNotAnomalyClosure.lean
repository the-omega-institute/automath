import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryDoubleEndOccupancy
import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch
import Omega.Conclusion.Window6CompletionThreefoldIncompressibility
import Omega.Conclusion.Window6NoLinearFactorization

namespace Omega.Conclusion

/-- Paper-facing package for
`prop:conclusion-window6-topological-closure-not-anomaly-closure`. -/
def conclusion_window6_topological_closure_not_anomaly_closure_statement : Prop :=
  full_fiber_partition_is_not_a_free_finite_group_orbit_partition ∧
    (¬ ∃ k, Omega.GU.TerminalFoldbin6CosetModel k) ∧
    window6BoundaryFiber.Nonempty ∧
    Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
    2 ^ 6 - Nat.fib 8 = 43

theorem conclusion_window6_topological_closure_not_anomaly_closure_holds :
    conclusion_window6_topological_closure_not_anomaly_closure_statement := by
  rcases paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch with ⟨_, hfree⟩
  rcases paper_conclusion_window6_boundary_double_end_occupancy with ⟨hboundary, _⟩
  rcases paper_conclusion_window6_completion_threefold_incompressibility with
    ⟨_, hcard, _, _, hhidden, _⟩
  refine ⟨hfree, paper_conclusion_window6_no_linear_factorization, ?_, hcard, hhidden⟩
  rw [hboundary]
  simp [conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words]

def paper_conclusion_window6_topological_closure_not_anomaly_closure : Prop := by
  exact conclusion_window6_topological_closure_not_anomaly_closure_statement

end Omega.Conclusion
