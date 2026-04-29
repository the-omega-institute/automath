import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Conclusion.FoldbinLikelihoodRatioTwoAtomTransfer

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-time-part70aa-binfold-all-real-moments-closed`. The verified two-atom
binfold likelihood-ratio law already computes the expectation of every test function; applying it
to the real-power test `x ↦ x^t` gives the closed formula for every real moment. -/
theorem paper_xi_time_part70aa_binfold_all_real_moments_closed (q : ℕ) :
    ∀ t : ℝ,
      Omega.Conclusion.foldbinLikelihoodRatioExpectation q (fun x => Real.rpow x t) =
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q) t +
        Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q) t ∧
      Omega.Conclusion.foldbinLikelihoodRatioExpectation q (fun x => Real.rpow x t) =
        (Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1))) *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q) t +
        (1 / (1 + Real.goldenRatio ^ (q + 1))) *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q) t := by
  intro t
  have htransfer :
      Omega.Conclusion.foldbinLikelihoodRatioExpectation q (fun x => Real.rpow x t) =
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q) t +
        Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q) t := by
    exact
      (Omega.Conclusion.paper_conclusion_foldbin_likelihood_ratio_two_atom_transfer q).2.2.2.2.1
        (fun x => Real.rpow x t)
  have hlow :
      Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q =
        1 / (1 + Real.goldenRatio ^ (q + 1)) := by
    exact (Omega.Conclusion.binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q).1
  have hhigh :
      Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q =
        Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) := by
    exact (Omega.Conclusion.binfoldTwoPointLimitLaw_holds Real.goldenRatio_pos q).2
  refine ⟨htransfer, ?_⟩
  calc
    Omega.Conclusion.foldbinLikelihoodRatioExpectation q (fun x => Real.rpow x t) =
        Omega.Conclusion.binfoldTwoPointLimitMassHigh Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q) t +
        Omega.Conclusion.binfoldTwoPointLimitMassLow Real.goldenRatio q *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q) t := htransfer
    _ =
        (Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1))) *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q) t +
        (1 / (1 + Real.goldenRatio ^ (q + 1))) *
          Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q) t := by
          rw [hhigh, hlow]

end

end Omega.Zeta
