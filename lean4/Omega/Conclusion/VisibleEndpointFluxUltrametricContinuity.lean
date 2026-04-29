import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-visible-endpoint-flux-ultrametric-continuity`.

If two endpoint fluxes use the same finite-prefix approximant and each has error at most
`C * q ^ N`, their distance is bounded by `2 * C * q ^ N`. -/
theorem paper_conclusion_visible_endpoint_flux_ultrametric_continuity
    (C q fluxAlpha fluxBeta sharedPrefix : ℝ) (N : ℕ)
    (hAlpha : |fluxAlpha - sharedPrefix| ≤ C * q ^ N)
    (hBeta : |fluxBeta - sharedPrefix| ≤ C * q ^ N) :
    |fluxAlpha - fluxBeta| ≤ 2 * C * q ^ N := by
  have htri :
      |fluxAlpha - fluxBeta| ≤ |fluxAlpha - sharedPrefix| + |sharedPrefix - fluxBeta| := by
    calc
      |fluxAlpha - fluxBeta| = |(fluxAlpha - sharedPrefix) + (sharedPrefix - fluxBeta)| := by
        ring_nf
      _ ≤ |fluxAlpha - sharedPrefix| + |sharedPrefix - fluxBeta| := abs_add_le _ _
  calc
    |fluxAlpha - fluxBeta|
        ≤ |fluxAlpha - sharedPrefix| + |sharedPrefix - fluxBeta| := htri
    _ ≤ C * q ^ N + C * q ^ N := by
        exact add_le_add hAlpha (by simpa [abs_sub_comm] using hBeta)
    _ = 2 * C * q ^ N := by ring

end Omega.Conclusion
