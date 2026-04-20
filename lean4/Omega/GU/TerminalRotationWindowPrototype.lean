import Mathlib.Tactic
import Omega.GU.TerminalCutProjectToFoldHist

namespace Omega.GU

/-- Paper label: `cor:terminal-rotation-window-prototype`.
The implementation-independent window-6 invariant is exactly the audited second component of the
cut-project-to-fold-hist theorem. -/
theorem paper_terminal_rotation_window_prototype : terminalCutProjectWindow6Invariant := by
  exact paper_terminal_cut_project_to_fold_hist.2

end Omega.GU
