import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the coincidence of decoding and presentation
    scales in the rigidity reconstruction section.
    cor:local-complexity-scale-coincidence -/
theorem paper_resolution_folding_local_complexity_scale_coincidence
    {m : ℕ} (_hm : 3 ≤ m)
    (sftOrder synchronizingLength nilpotencyIndex inverseMemory : ℕ)
    (windowLengthVisible : Prop)
    (hSFT : sftOrder = m)
    (hSync : synchronizingLength = m)
    (hNil : nilpotencyIndex = m)
    (hMem : inverseMemory = m - 1)
    (hWindow :
      sftOrder = m ∧ synchronizingLength = m ∧ nilpotencyIndex = m ∧ inverseMemory = m - 1 →
        windowLengthVisible) :
    sftOrder = m ∧
      synchronizingLength = m ∧
      nilpotencyIndex = m ∧
      inverseMemory = m - 1 ∧
      windowLengthVisible := by
  have hExact :
      sftOrder = m ∧ synchronizingLength = m ∧ nilpotencyIndex = m ∧ inverseMemory = m - 1 :=
    ⟨hSFT, hSync, hNil, hMem⟩
  exact ⟨hSFT, hSync, hNil, hMem, hWindow hExact⟩

end Omega.Folding
