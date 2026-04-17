import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias
import Omega.GU.TerminalWindow6LocalUpliftAdmissibility

namespace Omega.GU

/-- The `δ = 34` boundary package combines the arithmetic identity `F₉ = 34`, the pure boundary
alias channel, and the local uplift certificate `0, ±34`.
    cor:bdry-delta34-triple-identity -/
theorem paper_bdry_delta34_triple_identity :
    Nat.fib 9 = 34 ∧
      terminalFoldbin6BoundaryOffsets = ({34} : Finset Nat) ∧
      (∀ baseValue : Nat,
        terminalFoldbin6BoundaryAlias baseValue = ({baseValue, baseValue + 34} : Finset Nat)) ∧
      terminalWindow6LocalUpliftSet = ({0, 34, -34} : Finset ℤ) := by
  rcases fold6_tail_offsets with ⟨_, h9, _⟩
  refine ⟨h9, ?_, ?_, ?_⟩
  · simpa [h9] using (paper_terminal_foldbin6_boundary_pure_f9_alias 0).2.1
  · intro baseValue
    simpa [h9] using (paper_terminal_foldbin6_boundary_pure_f9_alias baseValue).2.2
  · simpa using paper_terminal_window6_local_uplift_admissibility

end Omega.GU
