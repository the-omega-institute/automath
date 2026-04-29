namespace Omega.Zeta

/-- Paper label: `cor:xi-poisson-cauchy-i1-over-kl-ratio-2m`. -/
theorem paper_xi_poisson_cauchy_i1_over_kl_ratio_2m
    (klAsymptotic dissipationIdentity i1Limit ratioLimit : Prop)
    (hkl : klAsymptotic)
    (hdiss : klAsymptotic -> dissipationIdentity)
    (hI : dissipationIdentity -> i1Limit)
    (hratio : dissipationIdentity -> ratioLimit) :
    i1Limit ∧ ratioLimit := by
  have hDissipation : dissipationIdentity := hdiss hkl
  exact ⟨hI hDissipation, hratio hDissipation⟩

end Omega.Zeta
