import Omega.Conclusion.BinfoldSinglePowerdivAsymptoticStatisticalCompleteness

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-one-powerdiv-generates-subcritical-experiment-class`.
The verified single-power-divergence completeness package already supplies both the recovered
`χ²` baseline scalar and the common asymptotic Blackwell datum; this theorem simply extracts
those two conclusion-facing components. -/
theorem paper_conclusion_binfold_one_powerdiv_generates_subcritical_experiment_class :
    twoAtomScalar2 Real.goldenRatio = BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline ∧
      BinfoldEscortBlackwellDatum.AsymptoticallyBlackwellEquivalent
        conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness_blackwell_datum := by
  exact ⟨paper_conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness.1,
    paper_conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness.2.2.2.2.2⟩

end Omega.Conclusion
