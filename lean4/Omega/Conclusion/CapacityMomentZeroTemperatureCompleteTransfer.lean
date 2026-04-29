import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-capacity-moment-zero-temperature-complete-transfer`. -/
theorem paper_conclusion_capacity_moment_zero_temperature_complete_transfer
    (capacityDeterminesTail tailDeterminesMoments momentsDetermineEndpoint : Prop)
    (hTail : capacityDeterminesTail)
    (hMoments : capacityDeterminesTail → tailDeterminesMoments)
    (hEndpoint : tailDeterminesMoments → momentsDetermineEndpoint) :
    tailDeterminesMoments ∧ momentsDetermineEndpoint := by
  have hTailCounts : tailDeterminesMoments := hMoments hTail
  exact ⟨hTailCounts, hEndpoint hTailCounts⟩

end Omega.Conclusion
