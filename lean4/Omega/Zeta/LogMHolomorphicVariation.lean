namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for holomorphic variation of the Abel finite part in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    thm:logM-holomorphic-variation -/
theorem paper_fredholm_witt_logM_holomorphic_variation
    (reducedDeterminantGradient normalCorrectionSeries holomorphicFinitePart
      primitiveLogMVariation : Prop)
    (hGradient : reducedDeterminantGradient)
    (hSeries : normalCorrectionSeries)
    (hHolomorphic :
      reducedDeterminantGradient → normalCorrectionSeries → holomorphicFinitePart)
    (hPrimitive : holomorphicFinitePart → primitiveLogMVariation) :
    holomorphicFinitePart ∧ primitiveLogMVariation := by
  have hFinitePart : holomorphicFinitePart := hHolomorphic hGradient hSeries
  exact ⟨hFinitePart, hPrimitive hFinitePart⟩

end Omega.Zeta
