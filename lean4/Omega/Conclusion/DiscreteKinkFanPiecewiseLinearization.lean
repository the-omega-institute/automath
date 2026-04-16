namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the discrete kink-fan linearization argument:
discrete convexity produces a convex piecewise-affine interpolation, identifies the node
subdifferential interval, and transfers discrete argmax points to the continuous
piecewise-linear objective.
    thm:conclusion-discrete-kink-fan-piecewise-linearization -/
theorem paper_conclusion_discrete_kink_fan_piecewise_linearization
    (discreteConvex piecewiseAffineConvex nodeSubdifferential argmaxEquivalence : Prop)
    (hConvex : discreteConvex → piecewiseAffineConvex)
    (hSubdiff : piecewiseAffineConvex → nodeSubdifferential)
    (hArgmax : piecewiseAffineConvex → argmaxEquivalence) :
    discreteConvex →
      discreteConvex ∧ piecewiseAffineConvex ∧ nodeSubdifferential ∧ argmaxEquivalence := by
  intro hDiscrete
  have hPiecewise : piecewiseAffineConvex := hConvex hDiscrete
  exact ⟨hDiscrete, hPiecewise, hSubdiff hPiecewise, hArgmax hPiecewise⟩

end Omega.Conclusion
