import Mathlib.Tactic
import Omega.GU.BoundaryDelta34TripleIdentity
import Omega.GU.BdryUpliftOrientationParity

namespace Omega.GU

/-- Paper-facing wrapper for the terminal `δ = 34` boundary alias and the canonical `ℤ/2`
sheet-parity law on the three boundary fibers.
    cor:terminal-delta-parity-rule -/
theorem paper_terminal_delta_parity_rule :
    Nat.fib 9 = 34 ∧
      terminalFoldbin6BoundaryOffsets = ({34} : Finset Nat) ∧
      (∀ baseValue : Nat,
        terminalFoldbin6BoundaryAlias baseValue = ({baseValue, baseValue + 34} : Finset Nat)) ∧
      Fintype.card (Fin 3) = 3 ∧
      (∀ _ : Fin 3, upliftOrientationParity 2 (Equiv.swap 0 1) = -1) := by
  rcases paper_bdry_delta34_triple_identity with ⟨hfib, hoffsets, halias, _⟩
  refine ⟨hfib, hoffsets, halias, by decide, ?_⟩
  intro _i
  exact upliftOrientationParity_two_swap

end Omega.GU
