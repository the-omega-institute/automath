import Omega.Conclusion.BinfoldEscortBlackwellEquivalence
import Omega.Conclusion.BinfoldEscortCsiszarBlackwellPhi
import Omega.Conclusion.BinfoldMellinEscortSemigroup
import Omega.Conclusion.Chi2RecoversFullPowerDivergenceFamily

namespace Omega.Conclusion

open Omega.Zeta

noncomputable section

/-- The common limiting Bernoulli experiment determined by the verified golden escort weight. -/
def conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness_blackwell_datum :
    BinfoldEscortBlackwellDatum :=
  { π := fun _ => xiEscortBlockLaw (xiEscortTheta 0)
    theta_m := fun _ => xiEscortTheta 0
    theta := xiEscortTheta 0
    C1 := 0
    C2 := 0
    hApprox := by
      intro m
      simp [xiEscortExactBlockLaw, xiEscortTvDistance, xiEscortBlockLaw]
    hTheta := by
      intro m
      simp }

/-- Paper label: `thm:conclusion-binfold-single-powerdiv-asymptotic-statistical-completeness`.

The verified `χ²` baseline scalar is already the fixed power-divergence witness. It recovers the
golden parameter, determines the explicit full power-divergence family, is compatible with the
escort/Csiszar wrapper, and all of these packages collapse to the same limiting Bernoulli
experiment. -/
theorem paper_conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness :
    twoAtomScalar2 Real.goldenRatio = BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline ∧
    Real.goldenRatio =
      (5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 3) / 2 ∧
    BinfoldMellinEscortSemigroup Real.goldenRatio ∧
    (∀ n : ℕ,
      conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data.spectrum n =
        conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data.leftWeight *
            Real.exp
              (Real.log
                  ((5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 3) / 2 /
                    (5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 2)) *
                n) +
          conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data.rightWeight *
            Real.exp
              (Real.log
                  (((5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 3) / 2) ^ 2 /
                    (5 * BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline + 2)) *
                n)) ∧
    (let D : BinfoldEscortCsiszarBlackwellPhiDatum := { p := 0, q := 1 }; D.Holds) ∧
    BinfoldEscortBlackwellDatum.AsymptoticallyBlackwellEquivalent
      conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness_blackwell_datum := by
  let Dchi : conclusion_chi2_recovers_full_power_divergence_family_data := {}
  let Descort : BinfoldEscortCsiszarBlackwellPhiDatum := { p := 0, q := 1 }
  have hchi := paper_conclusion_chi2_recovers_full_power_divergence_family Dchi
  have hescort := paper_conclusion_binfold_escort_csiszar_blackwell_phi Descort
  refine ⟨rfl, hescort.2.2.2.2, paper_conclusion_binfold_mellin_escort_semigroup, ?_, ?_, ?_⟩
  · intro n
    simpa [conclusion_chi2_recovers_full_power_divergence_family_chi2_constant] using hchi.2.2 n
  · simpa [Descort] using hescort
  · exact paper_conclusion_binfold_escort_blackwell_equivalence
      conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness_blackwell_datum

end

end Omega.Conclusion
