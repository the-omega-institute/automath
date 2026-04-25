import Omega.Conclusion.LkCentralBinomialCatalanMoments

open Filter Topology

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-Lk-normalized-trace-moments-central-binomial`. -/
theorem paper_conclusion_lk_normalized_trace_moments_central_binomial
    (r : ℕ) (traceMoment : ℕ → ℝ)
    (hconv : Tendsto traceMoment atTop (𝓝 (Omega.POM.arcsineAverage (fun μ => μ ^ r)))) :
    Tendsto traceMoment atTop (𝓝 (Nat.choose (2 * r) r : ℝ)) := by
  have hmoment := (paper_conclusion_lk_central_binomial_catalan_moments r).1
  simpa [hmoment] using hconv

end Omega.Conclusion
