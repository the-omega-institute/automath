import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6GeoSignAntiinvariant16
import Omega.GroupUnification.BdrySheetParityDiagonal

namespace Omega.GroupUnification

/-- The ten stable labels carrying odd geometric parity charge. The decimal values are the
binary words listed in the paper statement. -/
def window6GeoParityChargeSupport : Finset Nat :=
  {1, 4, 8, 9, 20, 21, 32, 34, 41, 42}

/-- The three audited boundary labels for window `6`. -/
def window6BoundaryWords : Finset Nat :=
  {33, 37, 41}

/-- Concrete package for the geometric parity-charge support and its boundary projection. -/
def Window6GeoParityChargeSupportBdryPackage : Prop :=
  window6GeoParityChargeSupport = ({1, 4, 8, 9, 20, 21, 32, 34, 41, 42} : Finset Nat) ∧
    window6GeoParityChargeSupport.card = 10 ∧
    window6GeoParityChargeSupport ∩ window6BoundaryWords = ({41} : Finset Nat) ∧
    Omega.GU.window6GeoTotalTwoCycles = 16 ∧
    bdrySheetParityDiagonalProjection 33 = false ∧
    bdrySheetParityDiagonalProjection 37 = false ∧
    bdrySheetParityDiagonalProjection 41 = true

/-- The odd-two-cycle geometric parity charge is supported on exactly ten stable labels, and its
boundary projection is the single `101001` axis.
    prop:window6-geo-parity-charge-support-bdry -/
theorem paper_window6_geo_parity_charge_support_bdry : Window6GeoParityChargeSupportBdryPackage := by
  rcases Omega.GU.paper_terminal_foldbin6_geo_sign_antiinvariant_16 with ⟨_, hTwo, _, _, _⟩
  rcases paper_bdry_sheet_parity_diagonal with ⟨_, _, _, _, _, _, h33, h37, h41⟩
  refine ⟨rfl, by native_decide, by native_decide, hTwo, h33, h37, h41⟩

end Omega.GroupUnification
