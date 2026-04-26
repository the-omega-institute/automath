namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-gauge-difference-cumulant-sign-oscillation`. -/
theorem paper_conclusion_realinput40_gauge_difference_cumulant_sign_oscillation
    (singularityTransfer cosineOscillation tailSignFailure : Prop)
    (hTransfer : singularityTransfer → cosineOscillation)
    (hOsc : cosineOscillation → tailSignFailure) :
    singularityTransfer → tailSignFailure := by
  intro hSingularity
  exact hOsc (hTransfer hSingularity)

end Omega.Conclusion
