namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-disjointness-exceptional-spectrum-reconstruction-from-qplus1-traces`.
-/
theorem paper_conclusion_disjointness_exceptional_spectrum_reconstruction_from_qplus1_traces
    (q : Nat) (traceDataAvailable exceptionalPowerSumsRecovered newtonReconstructsFactor : Prop)
    (hTrace : traceDataAvailable)
    (hSubtract : traceDataAvailable -> exceptionalPowerSumsRecovered)
    (hNewton : exceptionalPowerSumsRecovered -> newtonReconstructsFactor) :
    newtonReconstructsFactor := by
  have _hq : q = q := rfl
  exact hNewton (hSubtract hTrace)

end Omega.Conclusion
