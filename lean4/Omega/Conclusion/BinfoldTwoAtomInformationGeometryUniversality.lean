import Omega.Conclusion.FoldbinLikelihoodRatioTwoAtomTransfer

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-binfold-twoatom-information-geometry-universality`. -/
theorem paper_conclusion_binfold_twoatom_information_geometry_universality (q : ℕ) (f : ℝ → ℝ) :
    foldbinLikelihoodRatioExpectation q f =
      binfoldTwoPointLimitMassHigh Real.goldenRatio q * f (foldbinLikelihoodRatioLow q) +
        binfoldTwoPointLimitMassLow Real.goldenRatio q * f (foldbinLikelihoodRatioHigh q) := by
  rcases paper_conclusion_foldbin_likelihood_ratio_two_atom_transfer q with
    ⟨_, _, _, _, htransfer, _, _⟩
  exact htransfer f

end

end Omega.Conclusion
