import Omega.Conclusion.FibadicGoldenExtensionNoIntrinsicQ5Realization

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-qsqrtfive-cumulant-jet-escapes-q5`. -/
theorem paper_conclusion_realinput40_qsqrtfive_cumulant_jet_escapes_q5
    (D : conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_data)
    (cumulantJetInQ5 localModelKeepsClosedCoefficients containsSqrtFive ramifiedExtension : Prop)
    (hJetForcesQ5 : cumulantJetInQ5 → D.intrinsicQ5Realization)
    (hClosedForcesSqrtFive : localModelKeepsClosedCoefficients → containsSqrtFive)
    (hSqrtFiveForcesRamified : containsSqrtFive → ramifiedExtension) :
    ¬ cumulantJetInQ5 ∧ (localModelKeepsClosedCoefficients → ramifiedExtension) := by
  refine ⟨?_, ?_⟩
  · intro hJet
    exact paper_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization D
      (hJetForcesQ5 hJet)
  · intro hClosed
    exact hSqrtFiveForcesRamified (hClosedForcesSqrtFive hClosed)

end Omega.Conclusion
