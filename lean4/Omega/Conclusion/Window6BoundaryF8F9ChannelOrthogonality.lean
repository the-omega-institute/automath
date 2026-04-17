import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityNotMeasurableFromF8
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias

namespace Omega.Conclusion

open Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing separation theorem for the boundary `F₈/F₉` hidden channels: the `F₈` repair bit
is constant on every boundary fiber, canonical boundary parity flips across each fiber, and the
boundary alias layer is the pure `+34 = F₉` channel.
    thm:conclusion-window6-boundary-f8-f9-channel-orthogonality -/
theorem paper_conclusion_window6_boundary_f8_f9_channel_orthogonality :
    (∀ x y : Window6BoundaryPoint,
      window6BoundaryFiberIndex x = window6BoundaryFiberIndex y →
        window6F8RepairBit x = window6F8RepairBit y) ∧
    (∀ i : Fin 3,
      window6CanonicalBoundaryParity (i, false) ≠ window6CanonicalBoundaryParity (i, true)) ∧
    terminalFoldbin6BoundaryOffsets = {34} ∧
    (∀ baseValue : Nat, terminalFoldbin6BoundaryAlias baseValue = {baseValue, baseValue + 34}) ∧
    ¬ window6BoundaryMeasurableFromF8 window6CanonicalBoundaryParity := by
  rcases paper_conclusion_window6_boundary_parity_not_measurable_from_f8 with
    ⟨hConst, hAnti, hNotMeas, _⟩
  refine ⟨hConst, hAnti, ?_, ?_, hNotMeas⟩
  · simpa using (paper_terminal_foldbin6_boundary_pure_f9_alias 0).2.1
  · intro baseValue
    simpa using (paper_terminal_foldbin6_boundary_pure_f9_alias baseValue).2.2

end Omega.Conclusion
