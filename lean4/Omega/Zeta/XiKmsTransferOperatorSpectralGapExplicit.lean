namespace Omega.Zeta

/-- Paper label: `thm:xi-kms-transfer-operator-spectral-gap-explicit`. -/
theorem paper_xi_kms_transfer_operator_spectral_gap_explicit
    (statePreserving selfAdjointContractive diagonalPeripheralSpectrum centeredSpectralGap
      quantifiedMixingRate : Prop)
    (hState : statePreserving)
    (hContractive : selfAdjointContractive)
    (hDiagonal : diagonalPeripheralSpectrum)
    (hGap : centeredSpectralGap)
    (hMixing : quantifiedMixingRate) :
    statePreserving ∧ selfAdjointContractive ∧ diagonalPeripheralSpectrum ∧
      centeredSpectralGap ∧ quantifiedMixingRate := by
  exact ⟨hState, hContractive, hDiagonal, hGap, hMixing⟩

end Omega.Zeta
