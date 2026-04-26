namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-leyang-transport-zero-cloud-central-binomial`.
The three Lee--Yang transport conclusions are packaged as a single conjunction. -/
theorem paper_conclusion_leyang_transport_zero_cloud_central_binomial
    (oddMomentsVanish evenMomentsCentralBinomial radialSecondLimit : Prop)
    (hodd : oddMomentsVanish) (heven : evenMomentsCentralBinomial)
    (hrad : radialSecondLimit) :
    oddMomentsVanish ∧ evenMomentsCentralBinomial ∧ radialSecondLimit := by
  exact ⟨hodd, heven, hrad⟩

end Omega.Conclusion
