import Omega.POM.RqQinftyEndpoint

open Filter Topology

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing Perron--Landauer limit wrapper: once the tensor-kernel spectral radii satisfy
the chapter's standard `r_q^(1/q)` squeeze, the endpoint limit law is exactly the existing
`q → ∞` Perron-root package.
    thm:pom-perron-landauer-limit-law -/
theorem paper_pom_perron_landauer_limit_law
    (tensorPerronRoot landauerEntropyRate landauerDimension : ℕ → ℝ)
    (hbound : ∀ q, 2 ≤ q →
      Real.sqrt Real.goldenRatio ≤ tensorPerronRoot q ∧
        tensorPerronRoot q ≤
          Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ)))
    (hEntropy : ∀ q, 2 ≤ q →
      landauerEntropyRate q / (q : ℝ) = Real.log (2 / tensorPerronRoot q))
    (hDimension : ∀ q, 2 ≤ q →
      landauerDimension q =
        (landauerEntropyRate q / ((q : ℝ) - 1)) * (Real.log Real.goldenRatio)⁻¹) :
    Tendsto tensorPerronRoot atTop (𝓝 (Real.sqrt Real.goldenRatio)) ∧
      Tendsto (fun q => landauerEntropyRate q / (q : ℝ)) atTop
        (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) ∧
      Tendsto (fun q => landauerEntropyRate q / ((q : ℝ) - 1)) atTop
        (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) ∧
      Tendsto landauerDimension atTop
        (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio)) ∧
      ∀ q, 2 ≤ q →
        0 ≤ Real.log (2 / Real.sqrt Real.goldenRatio) - landauerEntropyRate q / (q : ℝ) ∧
          Real.log (2 / Real.sqrt Real.goldenRatio) - landauerEntropyRate q / (q : ℝ) ≤
            Real.log Real.goldenRatio / (q : ℝ) := by
  exact paper_pom_rq_qinfty_endpoint
    tensorPerronRoot landauerEntropyRate landauerDimension hbound hEntropy hDimension

end Omega.POM
