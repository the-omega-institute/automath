import Omega.GU.BoundaryDelta34TripleIdentity
import Omega.GU.TerminalDeltaParityRule

namespace Omega.GU

theorem paper_bdry_sheet_parity_discrete_breaking :
    terminalWindow6LocalUpliftSet = ({0, 34, -34} : Finset Int) ∧
      terminalFoldbin6BoundaryOffsets = ({34} : Finset Nat) ∧
      (∀ baseValue : Nat,
        terminalFoldbin6BoundaryAlias baseValue = ({baseValue, baseValue + 34} : Finset Nat)) ∧
      (∀ _ : Fin 3, upliftOrientationParity 2 (Equiv.swap 0 1) = -1) := by
  rcases paper_bdry_delta34_triple_identity with ⟨_, hoffsets, halias, huplift⟩
  rcases paper_terminal_delta_parity_rule with ⟨_, _, _, _, hparity⟩
  exact ⟨huplift, hoffsets, halias, hparity⟩

end Omega.GU
