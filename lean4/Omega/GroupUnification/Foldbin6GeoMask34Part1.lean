import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GroupUnification

/-- A bit-opposition/equality split for the window-6 geometric `±34` mask identity.
    cor:foldbin6-geo-mask-34-part1 -/
theorem paper_foldbin6_geo_mask_34_part1 (omega : Fin 6 -> Bool) :
    ((omega 0 != omega 4) -> geoStabilizerAction omega = omega) /\
      ((omega 0 = omega 4) ->
        binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = 34 \/
          binaryEncode6 (geoStabilizerAction omega) - binaryEncode6 omega = -34) := by
  constructor
  · intro hneq
    funext i
    fin_cases i
    · cases h0 : omega 0 <;> cases h4 : omega 4 <;>
        simp [geoStabilizerAction, h0, h4] at hneq ⊢
    · simp [geoStabilizerAction]
    · simp [geoStabilizerAction]
    · simp [geoStabilizerAction]
    · cases h0 : omega 0 <;> cases h4 : omega 4 <;>
        simp [geoStabilizerAction, h0, h4] at hneq ⊢
    · simp [geoStabilizerAction]
  · intro heq
    cases h0 : omega 0 <;> cases h4 : omega 4
    · left
      rw [geoStabilizer_mask_34]
      simp [h0, h4]
    · simp [h0, h4] at heq
    · simp [h0, h4] at heq
    · right
      rw [geoStabilizer_mask_34]
      simp [h0, h4]

end Omega.GroupUnification
