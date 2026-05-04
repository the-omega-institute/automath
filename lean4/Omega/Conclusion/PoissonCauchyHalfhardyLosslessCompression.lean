import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-cauchy-halfhardy-lossless-compression`. -/
theorem paper_conclusion_poisson_cauchy_halfhardy_lossless_compression
    (laurentRigidity conjugateSymmetry halfHardyRecover : Prop) (hrig : laurentRigidity)
    (hsym : conjugateSymmetry)
    (hrec : laurentRigidity → conjugateSymmetry → halfHardyRecover) :
    halfHardyRecover := by
  exact hrec hrig hsym

end Omega.Conclusion
