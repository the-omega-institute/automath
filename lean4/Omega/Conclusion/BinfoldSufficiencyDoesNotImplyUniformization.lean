import Mathlib.Tactic
import Omega.Conclusion.BinfoldSinglePowerdivAsymptoticStatisticalCompleteness

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-binfold-sufficiency-does-not-imply-uniformization`. -/
theorem paper_conclusion_binfold_sufficiency_does_not_imply_uniformization :
    twoAtomScalar2 Real.goldenRatio =
        BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline ∧
      BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline =
        (2 * Real.goldenRatio - 3) / 5 ∧
      0 < BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline ∧
      BinfoldEscortBlackwellDatum.AsymptoticallyBlackwellEquivalent
        conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness_blackwell_datum := by
  let Descort : BinfoldEscortCsiszarBlackwellPhiDatum := { p := 0, q := 1 }
  have hescort := paper_conclusion_binfold_escort_csiszar_blackwell_phi Descort
  have hbaseline :
      BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline =
        (2 * Real.goldenRatio - 3) / 5 := hescort.2.2.2.1
  have hphi_lower : (3 / 2 : ℝ) < Real.goldenRatio := by
    rw [Real.goldenRatio]
    have hsqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    nlinarith
  have hbaseline_pos :
      0 < BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline := by
    rw [hbaseline]
    nlinarith
  exact ⟨rfl, hbaseline, hbaseline_pos,
    paper_conclusion_binfold_escort_blackwell_equivalence
      conclusion_binfold_single_powerdiv_asymptotic_statistical_completeness_blackwell_datum⟩

end

end Omega.Conclusion
