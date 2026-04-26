import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.BoundaryLayer
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice

namespace Omega.Conclusion

/-- The three explicit boundary words singled out by the window-`6` audit. -/
def conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words : Finset (Fin 64) :=
  {w100001, w100101, w101001}

/-- Paper-facing window-`6` boundary package: the audited boundary layer is exactly the explicit
three-word list, and its cardinality agrees with the double-end occupancy count `cBoundaryCount 6`.
-/
def conclusion_window6_boundary_double_end_occupancy_statement : Prop :=
  window6BoundaryFiber = conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words ∧
    cBoundaryCount 6 =
      conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words.card

/-- Paper label: `thm:conclusion-window6-boundary-double-end-occupancy`. -/
theorem paper_conclusion_window6_boundary_double_end_occupancy :
    conclusion_window6_boundary_double_end_occupancy_statement := by
  rcases paper_conclusion_window6_minimal_shell_rigid_subcover_root_slice with
    ⟨_, hboundary, _, hboundary_card, _, _⟩
  have hboundary' :
      window6BoundaryFiber =
        conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words := by
    simpa [conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words] using hboundary
  refine ⟨hboundary', ?_⟩
  calc
    cBoundaryCount 6 = 3 := cBoundaryCount_six
    _ = window6BoundaryFiber.card := hboundary_card.symm
    _ = conclusion_window6_boundary_double_end_occupancy_explicit_boundary_words.card := by
          rw [hboundary']

end Omega.Conclusion
