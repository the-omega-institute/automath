import Omega.GroupUnification.Foldbin6GeoStabilizerZ2
import Omega.GU.TerminalFoldbin6BdryUniqueGeoSelectedAxis

namespace Omega.GroupUnification

/-- The audited boundary fiber over `100001`. -/
def bdryFiber100001Datum : Omega.GU.TerminalFoldbin6TwoPointFiberDatum :=
  { fiberValue := 14
    leftPreimage := 14
    rightPreimage := 48
    direction := 62
    geoLeftImage := 14
    geoRightImage := 48 }

/-- The audited boundary fiber over `100101`. -/
def bdryFiber100101Datum : Omega.GU.TerminalFoldbin6TwoPointFiberDatum :=
  { fiberValue := 19
    leftPreimage := 19
    rightPreimage := 53
    direction := 38
    geoLeftImage := 19
    geoRightImage := 53 }

/-- The audited boundary fiber over `101001`. -/
def bdryFiber101001Datum : Omega.GU.TerminalFoldbin6TwoPointFiberDatum :=
  { fiberValue := 17
    leftPreimage := 17
    rightPreimage := 51
    direction := 34
    geoLeftImage := 51
    geoRightImage := 17 }

/-- The involution is pointwise fixed on the given boundary two-point fiber. -/
def bdryFiberDatumFixed (d : Omega.GU.TerminalFoldbin6TwoPointFiberDatum) : Prop :=
  d.geoLeftImage = d.leftPreimage ∧ d.geoRightImage = d.rightPreimage

/-- The involution swaps the two endpoints of the given boundary two-point fiber. -/
def bdryFiberDatumSwapped (d : Omega.GU.TerminalFoldbin6TwoPointFiberDatum) : Prop :=
  d.geoLeftImage = d.rightPreimage ∧ d.geoRightImage = d.leftPreimage

/-- The boundary-center projection selected by the geometric involution: only the `34`-direction
survives as the visible `Z/2` coordinate. -/
def bdrySheetParityDiagonalProjection (w : Nat) : Bool :=
  decide (Omega.GU.boundaryDirectionOfWord6 w = 34)

/-- The audited boundary two-point fibers over `100001` and `100101` are fixed pointwise by the
explicit geometric involution, while the fiber over `101001` is swapped; equivalently the induced
boundary-center projection is the single `101001` axis.
    cor:bdry-sheet-parity-diagonal -/
theorem paper_bdry_sheet_parity_diagonal :
    bdryFiber100001Datum ∈ Omega.GU.terminalFoldbin6TwoPointFiberData ∧
      bdryFiberDatumFixed bdryFiber100001Datum ∧
      bdryFiber100101Datum ∈ Omega.GU.terminalFoldbin6TwoPointFiberData ∧
      bdryFiberDatumFixed bdryFiber100101Datum ∧
      bdryFiber101001Datum ∈ Omega.GU.terminalFoldbin6TwoPointFiberData ∧
      bdryFiberDatumSwapped bdryFiber101001Datum ∧
      bdrySheetParityDiagonalProjection 33 = false ∧
      bdrySheetParityDiagonalProjection 37 = false ∧
      bdrySheetParityDiagonalProjection 41 = true := by
  rcases Omega.GU.paper_terminal_foldbin6_two_point_fiber_direction_spectrum with
    ⟨hdata, _, _, _, _, _⟩
  rcases Omega.GU.paper_terminal_foldbin6_bdry_unique_geo_selected_axis with
    ⟨h41, h37, h33⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hdata, bdryFiber100001Datum]
  · simp [bdryFiberDatumFixed, bdryFiber100001Datum]
  · simp [hdata, bdryFiber100101Datum]
  · simp [bdryFiberDatumFixed, bdryFiber100101Datum]
  · simp [hdata, bdryFiber101001Datum]
  · simp [bdryFiberDatumSwapped, bdryFiber101001Datum]
  · simp [bdrySheetParityDiagonalProjection, h33]
  · simp [bdrySheetParityDiagonalProjection, h37]
  · simp [bdrySheetParityDiagonalProjection, h41]

end Omega.GroupUnification
