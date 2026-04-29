namespace Omega.Zeta

/-- Paper label: `prop:xi-leyang-angle-over-pi-irrational`. -/
theorem paper_xi_leyang_angle_over_pi_irrational
    (thetaOverPiRational zetaRootOfUnity zetaAllowedByBiquadraticField zetaReal
      zetaNonreal : Prop)
    (hRat : thetaOverPiRational → zetaRootOfUnity)
    (hClassify : zetaRootOfUnity → zetaAllowedByBiquadraticField)
    (hAllowedReal : zetaAllowedByBiquadraticField → zetaReal)
    (hContradiction : zetaReal → zetaNonreal → False) (hNonreal : zetaNonreal) :
    ¬ thetaOverPiRational := by
  intro hTheta
  exact hContradiction (hAllowedReal (hClassify (hRat hTheta))) hNonreal

end Omega.Zeta
