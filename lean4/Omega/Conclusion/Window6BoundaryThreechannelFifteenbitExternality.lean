import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_window6_boundary_threechannel_fifteenbit_externality
    (rankT externalBits rFaith visibleBits centerBits : Nat) (hrFaith : rFaith = 3)
    (hrank : rFaith ≤ rankT) (hcenter : centerBits = 17) (hvisible : visibleBits = 2)
    (hexternal : externalBits = centerBits - visibleBits) : 3 ≤ rankT ∧ externalBits = 15 := by
  constructor <;> omega

end Omega.Conclusion
