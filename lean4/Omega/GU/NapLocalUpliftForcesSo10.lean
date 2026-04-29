import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.NapSo10AnalyticMinimality
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias

namespace Omega.GU

/-- Paper-facing corollary: the window-6 local uplift fixes the top offset to `F₉`, and the
registered NAP minimality package then identifies the `so(10)` dimension `45`.
    cor:nap-local-uplift-forces-so10 -/
theorem paper_gut_nap_local_uplift_forces_so10 :
    terminalFoldbin6BoundaryOffsets = {Nat.fib 9} ∧ 45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by
  refine ⟨?_, Omega.GU.NapSo10AnalyticMinimality.paper_gut_nap_so10_analytic_minimality_package⟩
  exact (paper_terminal_foldbin6_boundary_pure_f9_alias 0).2.1

/-- Paper label wrapper under the published corollary slug.
    cor:nap-local-uplift-forces-so10 -/
theorem paper_nap_local_uplift_forces_so10 :
    terminalFoldbin6BoundaryOffsets = {Nat.fib 9} ∧ 45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by
  refine
    ⟨(paper_terminal_foldbin6_boundary_pure_f9_alias 0).2.1,
      Omega.GU.NapSo10AnalyticMinimality.paper_gut_nap_so10_analytic_minimality_package⟩

end Omega.GU
