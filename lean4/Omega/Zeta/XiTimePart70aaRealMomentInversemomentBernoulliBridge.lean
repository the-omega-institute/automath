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

/-- The inverse odd moment test exponent attached to the `r`th Bernoulli coefficient. -/
def xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_exponent
    (r : ℕ) : ℝ :=
  -((2 * r - 1 : ℕ) : ℝ)

/-- Concrete inverse odd moment specialization of the all-real-moments formula. -/
def xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_statement
    (r : ℕ) : Prop :=
  ∀ q : ℕ,
    Omega.Conclusion.foldbinLikelihoodRatioExpectation q
        (fun x =>
          Real.rpow x
            (xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_exponent r)) =
      (Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1))) *
        Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioLow q)
          (xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_exponent r) +
      (1 / (1 + Real.goldenRatio ^ (q + 1))) *
        Real.rpow (Omega.Conclusion.foldbinLikelihoodRatioHigh q)
          (xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_exponent r)

/-- Paper label:
`cor:xi-time-part70aa-bernoulli-coefficient-inverse-moment-interpretation`. -/
theorem paper_xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation
    (r : ℕ) (hr : 1 ≤ r) :
    xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_statement r := by
  intro q
  let _ := hr
  exact (paper_xi_time_part70aa_binfold_all_real_moments_closed q
    (xi_time_part70aa_bernoulli_coefficient_inverse_moment_interpretation_exponent r)).2

end

end Omega.Zeta
