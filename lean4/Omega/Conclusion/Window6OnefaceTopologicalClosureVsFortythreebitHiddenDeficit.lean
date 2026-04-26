import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.FullInternalVisibilityUniqueGlobalMode
import Omega.Conclusion.Window6CompletionThreefoldIncompressibility
import Omega.Conclusion.Window6NoLinearFactorization

namespace Omega.Conclusion

/-- Concrete wrapper data for the window-`6` one-face topological closure package. -/
structure conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_data where
  conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_witness :
    Unit := ()

namespace conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_data

/-- Paper-facing package for the `(m,n) = (1,6)` one-face closure audit and the `43`-bit hidden
deficit. -/
def statement
    (_D : conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_data) :
    Prop :=
  Omega.SPG.CoordinateBundleScreenCount.auditCost 1 6 6 = 1 ∧
    (∀ B : Finset ℕ, B.Nonempty →
      conclusion_full_internal_visibility_unique_global_mode_boundaryDefect 1 6 B = 0) ∧
    (¬ ∃ k, Omega.GU.TerminalFoldbin6CosetModel k) ∧
    2 ^ 6 - Nat.fib 8 = 43 ∧
    Nat.fib 8 + 43 = 2 ^ 6

end conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_data

/-- Paper label: `thm:conclusion-window6-oneface-topological-closure-vs-fortythreebit-hidden-deficit`.
At `(m,n) = (1,6)`, the full internal screen has audit cost `1`, any nonempty added boundary
family removes that last defect, and the visible/hidden split leaves the exact `43`-bit hidden
gap already verified in the window-`6` incompressibility package. -/
theorem paper_conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit
    (D : conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_data) :
    conclusion_window6_oneface_topological_closure_vs_fortythreebit_hidden_deficit_data.statement D := by
  rcases paper_conclusion_full_internal_visibility_unique_global_mode 1 6 with
    ⟨_, _, _, hboundary⟩
  rcases paper_conclusion_window6_completion_threefold_incompressibility with
    ⟨_, _, _, _, hhidden, hbudget⟩
  refine ⟨?_, hboundary, paper_conclusion_window6_no_linear_factorization, hhidden, hbudget⟩
  norm_num [Omega.SPG.CoordinateBundleScreenCount.auditCost]

end Omega.Conclusion
