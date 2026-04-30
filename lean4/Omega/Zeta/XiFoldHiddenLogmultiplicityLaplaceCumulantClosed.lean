import Omega.Zeta.XiFoldHiddenLogmultiplicityBranchbitTwoPointLaw

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-hidden-logmultiplicity-laplace-cumulant-closed`. -/
theorem paper_xi_fold_hidden_logmultiplicity_laplace_cumulant_closed
    (twoPointLaw laplaceUniformAsymptotic laplaceLimit cumulantsConverge
      firstFourCumulants nonGaussianCore : Prop)
    (hBranch : twoPointLaw)
    (hAsymp : twoPointLaw → laplaceUniformAsymptotic)
    (hLimit : laplaceUniformAsymptotic → laplaceLimit)
    (hCumulants : laplaceLimit → cumulantsConverge)
    (hFirstFour : cumulantsConverge → firstFourCumulants)
    (hNonGaussian : firstFourCumulants → nonGaussianCore) :
    laplaceUniformAsymptotic ∧ laplaceLimit ∧ cumulantsConverge ∧
      firstFourCumulants ∧ nonGaussianCore := by
  have hTwoPoint : twoPointLaw :=
    (paper_xi_fold_hidden_logmultiplicity_branchbit_two_point_law twoPointLaw
      laplaceUniformAsymptotic twoPointLaw (fun h => h) hAsymp hBranch).1
  have hLaplaceUniformAsymptotic : laplaceUniformAsymptotic := hAsymp hTwoPoint
  have hLaplaceLimit : laplaceLimit := hLimit hLaplaceUniformAsymptotic
  have hCumulantsConverge : cumulantsConverge := hCumulants hLaplaceLimit
  have hFirstFourCumulants : firstFourCumulants := hFirstFour hCumulantsConverge
  exact
    ⟨hLaplaceUniformAsymptotic, hLaplaceLimit, hCumulantsConverge, hFirstFourCumulants,
      hNonGaussian hFirstFourCumulants⟩

end Omega.Zeta
