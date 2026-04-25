namespace Omega.Zeta

/-- Paper label: `cor:xi-phiL-toeplitz-length-lb-delta-min`. -/
theorem paper_xi_phil_toeplitz_length_lb_delta_min
    (toeplitzPoleDetected certificateLengthLowerBound thinLayerAsymptotic : Prop)
    (hPole : toeplitzPoleDetected)
    (hLength : toeplitzPoleDetected → certificateLengthLowerBound)
    (hThin : certificateLengthLowerBound → thinLayerAsymptotic) :
    certificateLengthLowerBound ∧ thinLayerAsymptotic := by
  exact ⟨hLength hPole, hThin (hLength hPole)⟩

end Omega.Zeta
