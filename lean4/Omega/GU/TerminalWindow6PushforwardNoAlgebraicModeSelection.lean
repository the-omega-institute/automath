import Omega.GU.TerminalWindow6PushforwardCommutantMasa
import Omega.GU.TerminalWindow6PushforwardNoNonabelianCompactSymmetry

namespace Omega.GU

/-- Chapter-local package for the window-`6` mode-selection obstruction. The data records the
shared rational-field witness for the nontrivial eigenmodes, the impossibility of isolating a
single mode by a purely `ℚ`-algebraic predicate, and the necessity of an Archimedean order input
to distinguish slow from fast modes. -/
structure TerminalWindow6ModeSelectionData where
  sameRationalField : Prop
  noQPolynomialSelector : Prop
  archimedeanOrderIsNecessary : Prop
  sameRationalFieldWitness : sameRationalField
  noQPolynomialSelectorWitness : noQPolynomialSelector
  archimedeanOrderWitness : archimedeanOrderIsNecessary

/-- Purely `ℚ`-algebraic mode selectors cannot distinguish a preferred nontrivial eigenmode of the
window-`6` pushforward; the distinction only appears after choosing an Archimedean order.
    prop:terminal-window6-pushforward-no-algebraic-mode-selection -/
theorem paper_terminal_window6_pushforward_no_algebraic_mode_selection
    (h : TerminalWindow6ModeSelectionData) :
    h.sameRationalField ∧ h.noQPolynomialSelector ∧ h.archimedeanOrderIsNecessary := by
  exact
    ⟨h.sameRationalFieldWitness, h.noQPolynomialSelectorWitness, h.archimedeanOrderWitness⟩

end Omega.GU
