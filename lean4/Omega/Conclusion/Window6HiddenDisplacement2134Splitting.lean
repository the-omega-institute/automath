import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-hidden-displacement-21-34-splitting`.
The Markov obstruction and geometric uplift hypotheses combine into the F8/F9 separation. -/
theorem paper_conclusion_window6_hidden_displacement_21_34_splitting
    (markovF8 geometricF9 noCommonLocalMechanism : Prop)
    (hMarkov : markovF8)
    (hGeom : geometricF9)
    (hsplit : markovF8 -> geometricF9 -> noCommonLocalMechanism) :
    noCommonLocalMechanism := by
  exact hsplit hMarkov hGeom

end Omega.Conclusion
