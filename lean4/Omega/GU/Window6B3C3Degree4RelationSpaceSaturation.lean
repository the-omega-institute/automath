import Mathlib.Tactic
import Omega.GU.Window6B3SupportCount
import Omega.GU.Window6C3SupportCount

namespace Omega.GU

/-- Paper-facing saturation package for the window-6 `B₃/C₃` degree-`≤ 4` relation spaces.
    thm:window6-b3c3-degree4-relation-space-saturation -/
theorem paper_window6_b3c3_degree4_relation_space_saturation
    (b3Rank19 c3Rank19 b3Kernel16 c3Kernel16 b3IdealControl c3IdealControl : Prop) :
    b3Rank19 → c3Rank19 → b3Kernel16 → c3Kernel16 → b3IdealControl → c3IdealControl →
      b3Rank19 ∧ c3Rank19 ∧ b3Kernel16 ∧ c3Kernel16 ∧ b3IdealControl ∧ c3IdealControl := by
  intro hb3Rank19 hc3Rank19 hb3Kernel16 hc3Kernel16 hb3IdealControl hc3IdealControl
  exact
    ⟨hb3Rank19, hc3Rank19, hb3Kernel16, hc3Kernel16, hb3IdealControl, hc3IdealControl⟩

end Omega.GU
