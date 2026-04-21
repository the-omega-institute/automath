import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Admissible stages in the audited window-6 figure protocol. -/
inductive Window6FigureStage where
  | visibleSpectrum
  | boundaryHolonomy
  | budgetSplit
  | fixedWindowCollision
  | roughVisibility
  | blockCollision
  | boundaryUpliftGate
  deriving DecidableEq, Repr

/-- Recommended presentation order for the window-6 figure table. -/
def window6FigureTableOrder : List Window6FigureStage :=
  [Window6FigureStage.visibleSpectrum, Window6FigureStage.boundaryHolonomy,
    Window6FigureStage.budgetSplit, Window6FigureStage.fixedWindowCollision,
    Window6FigureStage.roughVisibility, Window6FigureStage.blockCollision,
    Window6FigureStage.boundaryUpliftGate]

/-- Paper label: `prop:typed-address-biaxial-completion-window6-figure-table-order`. -/
theorem paper_typed_address_biaxial_completion_window6_figure_table_order :
    window6FigureTableOrder = [Window6FigureStage.visibleSpectrum,
      Window6FigureStage.boundaryHolonomy, Window6FigureStage.budgetSplit,
      Window6FigureStage.fixedWindowCollision, Window6FigureStage.roughVisibility,
      Window6FigureStage.blockCollision, Window6FigureStage.boundaryUpliftGate] := by
  rfl

end Omega.TypedAddressBiaxialCompletion
