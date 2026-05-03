import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-center-unique-extremal-bridge`. -/
theorem paper_conclusion_window6_boundary_center_unique_extremal_bridge
    (Dir Fiber : Type) (weight : Dir → ℕ) (realizes : Fiber → Dir → Prop)
    (b1 b2 xi : Dir) (fcyc fbdry : Fiber)
    (hweights : weight b1 = 2 ∧ weight b2 = 3 ∧ weight xi = 5)
    (huniq : ∀ d, d = b1 ∨ d = b2 ∨ d = xi → weight d = 5 → d = xi)
    (hreal : ∀ f d, realizes f d ↔ d = xi ∧ (f = fcyc ∨ f = fbdry)) :
    (∀ d, d = b1 ∨ d = b2 ∨ d = xi → (weight d = 5 ↔ d = xi)) ∧
      (∀ f d, realizes f d ↔ d = xi ∧ (f = fcyc ∨ f = fbdry)) := by
  constructor
  · intro d hd
    constructor
    · intro hw
      exact huniq d hd hw
    · intro hxi
      rw [hxi]
      exact hweights.2.2
  · exact hreal

end Omega.Conclusion
