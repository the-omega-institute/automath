import Omega.Zeta.XiCartesianPowerLeyangDoubleAtomTangentClt

namespace Omega.Zeta

/-- Paper label: `thm:xi-hypercube-dimension-readable-from-leyang-angular-variance`.
The Cartesian-power Lee--Yang tangent CLT wrapper packages the moment and Taylor inputs; the
second-moment and inverse-dimension asymptotics are then read out by the supplied implications. -/
theorem paper_xi_hypercube_dimension_readable_from_leyang_angular_variance
    (binomialCentralMoments arccosTaylorAtHalfPi secondMomentAsymptotic
      inverseDimensionAsymptotic : Prop)
    (hMoments : binomialCentralMoments)
    (hTaylor : arccosTaylorAtHalfPi)
    (hSecond : binomialCentralMoments → arccosTaylorAtHalfPi → secondMomentAsymptotic)
    (hInverse : secondMomentAsymptotic → inverseDimensionAsymptotic) :
    secondMomentAsymptotic ∧ inverseDimensionAsymptotic := by
  have hClt :=
    paper_xi_cartesian_power_leyang_double_atom_tangent_clt
      binomialCentralMoments arccosTaylorAtHalfPi binomialCentralMoments
      hMoments hTaylor hMoments
  have hSecondMoment : secondMomentAsymptotic := hSecond hClt.1 hClt.2.1
  exact ⟨hSecondMoment, hInverse hSecondMoment⟩

end Omega.Zeta
