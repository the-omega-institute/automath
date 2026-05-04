namespace Omega.Conclusion

/-- Histogram factorization forces the orbit ambiguity obstructing boundary recovery. -/
theorem conclusion_window6_boundary_parity_histogram_nonrecoverability_orbit_obstruction
    (histogramFactorization boundaryRecovered orbitAmbiguity : Prop)
    (hOrbit : histogramFactorization → orbitAmbiguity)
    (hNoRecover : orbitAmbiguity → ¬ boundaryRecovered) :
    histogramFactorization → ¬ boundaryRecovered := by
  intro hHistogram
  exact hNoRecover (hOrbit hHistogram)

/-- Paper label: `thm:conclusion-window6-boundary-parity-histogram-nonrecoverability`. -/
theorem paper_conclusion_window6_boundary_parity_histogram_nonrecoverability
    (histogramFactorization boundaryRecovered orbitAmbiguity : Prop)
    (hOrbit : histogramFactorization → orbitAmbiguity)
    (hNoRecover : orbitAmbiguity → ¬ boundaryRecovered) :
    histogramFactorization → ¬ boundaryRecovered := by
  exact conclusion_window6_boundary_parity_histogram_nonrecoverability_orbit_obstruction
    histogramFactorization boundaryRecovered orbitAmbiguity hOrbit hNoRecover

end Omega.Conclusion
