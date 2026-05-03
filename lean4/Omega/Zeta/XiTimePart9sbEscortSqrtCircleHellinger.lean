import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Omega.Conclusion.BinfoldEscortSqrtCircleArc

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9sb-escort-sqrt-circle-hellinger`. -/
theorem paper_xi_time_part9sb_escort_sqrt_circle_hellinger :
    (∀ q : Nat,
      Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi q =
        (Real.cos (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_alpha q),
          Real.sin (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_alpha q))) ∧
      (∀ p q : Nat,
        (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi p).1 *
            (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi q).1 +
          (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi p).2 *
            (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi q).2 =
          Real.cos
            (Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_alpha p -
              Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_alpha q)) := by
  constructor
  · intro q
    exact Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi_eq q
  · intro p q
    rw [Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi_eq p,
      Omega.Conclusion.conclusion_binfold_escort_sqrt_circle_arc_Xi_eq q]
    rw [Real.cos_sub]

end Omega.Zeta
