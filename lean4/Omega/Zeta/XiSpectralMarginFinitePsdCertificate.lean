namespace Omega.Zeta

/-- Paper label: `thm:xi-spectral-margin-finite-psd-certificate`. -/
theorem paper_xi_spectral_margin_finite_psd_certificate
    (finiteMargin errorControlled coefficientErrorControlled exactToeplitzPsd : Prop)
    (hWeyl : finiteMargin -> errorControlled -> exactToeplitzPsd)
    (hToeplitzNorm : coefficientErrorControlled -> errorControlled) :
    finiteMargin -> coefficientErrorControlled -> exactToeplitzPsd := by
  intro hMargin hCoeff
  exact hWeyl hMargin (hToeplitzNorm hCoeff)

end Omega.Zeta
