namespace Omega.Zeta

/-- Paper package for the dominant-zero Hankel pencil construction.
    thm:xi-leyang-hankel-pencil-dominant-zeros -/
theorem paper_xi_leyang_hankel_pencil_dominant_zeros
    (dominantGap hankelPencilDefined exponentialSpectralApproximation
      recoveredZerosExponentially : Prop)
    (hConstruct : dominantGap -> hankelPencilDefined)
    (hApprox : hankelPencilDefined -> exponentialSpectralApproximation)
    (hRecover : exponentialSpectralApproximation -> recoveredZerosExponentially) :
    dominantGap ->
      hankelPencilDefined ∧ exponentialSpectralApproximation ∧ recoveredZerosExponentially := by
  intro hDominant
  have hPencil : hankelPencilDefined := hConstruct hDominant
  have hSpectral : exponentialSpectralApproximation := hApprox hPencil
  exact ⟨hPencil, hSpectral, hRecover hSpectral⟩

end Omega.Zeta
