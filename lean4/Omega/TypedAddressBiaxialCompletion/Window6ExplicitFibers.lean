import Omega.Folding.BinFold
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias
import Omega.GU.TerminalFoldbin6ThreeOffsetRigidity

namespace Omega.TypedAddressBiaxialCompletion

open Omega.GU

/-- Typed-address-facing packaging of the explicit window-6 fiber data: the hidden offset set is
`{21,34,55}`, the nontrivial fiber histogram is `8/4/9`, and the boundary sector is the pure
`F₉ = 34` two-sheet alias. -/
theorem paper_typed_address_biaxial_completion_window6_explicit_fibers (baseValue : Nat) :
    terminalFoldbin6TailOffsets = {21, 34, 55} ∧ cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧
      cBinFiberHist 6 4 = 9 ∧
      terminalFoldbin6BoundaryAlias baseValue = {baseValue, baseValue + 34} := by
  refine ⟨rfl, cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4, rfl⟩

end Omega.TypedAddressBiaxialCompletion
