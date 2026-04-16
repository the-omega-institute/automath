import Mathlib.Tactic
import Omega.GU.ZeckendorfCountClosure

namespace Omega.GU

/-- The window-6 tail-offset set. -/
def terminalFoldbin6TailOffsets : Finset Nat :=
  {21, 34, 55}

/-- The boundary sector keeps only the middle `F₉ = 34` offset. -/
def terminalFoldbin6BoundaryOffsets : Finset Nat :=
  {34}

/-- The corresponding boundary alias pair over a base value `V₆(w)`. -/
def terminalFoldbin6BoundaryAlias (baseValue : Nat) : Finset Nat :=
  {baseValue, baseValue + 34}

/-- Paper wrapper for the boundary-sector pure `F₉` alias at window 6.
    cor:terminal-foldbin6-boundary-pure-f9-alias -/
theorem paper_terminal_foldbin6_boundary_pure_f9_alias (baseValue : Nat) :
    terminalFoldbin6TailOffsets = {Nat.fib 8, Nat.fib 9, Nat.fib 10} ∧
    terminalFoldbin6BoundaryOffsets = {Nat.fib 9} ∧
    terminalFoldbin6BoundaryAlias baseValue = {baseValue, baseValue + Nat.fib 9} := by
  rcases fold6_tail_offsets with ⟨h8, h9, h10⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [terminalFoldbin6TailOffsets, h8, h9, h10]
  · simp [terminalFoldbin6BoundaryOffsets, h9]
  · simp [terminalFoldbin6BoundaryAlias, h9]

end Omega.GU
