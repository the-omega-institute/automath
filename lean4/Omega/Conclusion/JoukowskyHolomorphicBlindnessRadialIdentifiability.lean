import Omega.GU.RadialQuadraticIdentifiability

namespace Omega.Conclusion

/-- Conclusion-level wrapper for the Joukowsky holomorphic blindness and radial inversion pair.
    thm:conclusion-joukowsky-holomorphic-blindness-radial-identifiability -/
theorem paper_conclusion_joukowsky_holomorphic_blindness_radial_identifiability (r : ℝ)
    (hr : 1 ≤ r) :
    Omega.GU.RadialQuadraticIdentifiability.holomorphicMomentBlindness r ∧
      Omega.EA.JoukowskyEllipse.primeRegisterJoukowskyRadialMomentInvert r := by
  exact
    Omega.GU.RadialQuadraticIdentifiability.paper_group_jg_minimal_radial_identifiability_threshold
      r hr

end Omega.Conclusion
