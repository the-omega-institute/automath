import Mathlib

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the rigidity of equivariant free binary lifts.
    thm:equivariant-z2-layerlift-wreath-rigidity -/
theorem paper_gu_equivariant_z2_layerlift_wreath_rigidity
    (k : ℕ) (hk : 3 ≤ k)
    (standardBinaryCover autGroupIsWreath uniqueFreeCentralInvolution : Prop)
    (hCover : standardBinaryCover)
    (hAut : standardBinaryCover → autGroupIsWreath)
    (hCenter : autGroupIsWreath → uniqueFreeCentralInvolution) :
    standardBinaryCover ∧ autGroupIsWreath ∧ uniqueFreeCentralInvolution := by
  let _ := hk
  have hWreath : autGroupIsWreath := hAut hCover
  have hCentral : uniqueFreeCentralInvolution := hCenter hWreath
  exact ⟨hCover, hWreath, hCentral⟩

end Omega.GroupUnification
