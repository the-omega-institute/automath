namespace Omega.POM

/-- Paper label: `prop:pom-mom-lift-fourier-distribution`. -/
theorem paper_pom_mom_lift_fourier_distribution
    (q : Nat) (hq : 2 ≤ q)
    (fiberCounts fourierCoefficients neutralCharacterMomentIdentity : Prop)
    (hFourier : fiberCounts → fourierCoefficients)
    (hOrthogonality : fourierCoefficients → neutralCharacterMomentIdentity) :
    fiberCounts → neutralCharacterMomentIdentity := by
  have pom_mom_lift_fourier_distribution_q_ge_two : 2 ≤ q := hq
  intro hFiberCounts
  have pom_mom_lift_fourier_distribution_fourierCoefficients : fourierCoefficients :=
    hFourier hFiberCounts
  exact hOrthogonality pom_mom_lift_fourier_distribution_fourierCoefficients

end Omega.POM
