namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-puiseux-zero-scaling`. -/
theorem paper_xi_leyang_puiseux_zero_scaling
    (puiseuxExpansion strictSubdominant nonexponentialAmplitude zeroAsymptotic
      clusteringScale : Prop)
    (hzero : puiseuxExpansion -> strictSubdominant -> nonexponentialAmplitude -> zeroAsymptotic)
    (hscale : zeroAsymptotic -> clusteringScale)
    (hp : puiseuxExpansion) (hr : strictSubdominant) (ha : nonexponentialAmplitude) :
    zeroAsymptotic ∧ clusteringScale := by
  have hz : zeroAsymptotic := hzero hp hr ha
  exact ⟨hz, hscale hz⟩

end Omega.Zeta
