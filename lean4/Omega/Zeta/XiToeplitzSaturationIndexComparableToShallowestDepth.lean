namespace Omega.Zeta

/-- Paper label: `cor:xi-toeplitz-saturation-index-comparable-to-shallowest-depth`. -/
theorem paper_xi_toeplitz_saturation_index_comparable_to_shallowest_depth
    (reciprocalDepthBounds highHeightAsymptotic : Prop)
    (hBounds : reciprocalDepthBounds)
    (hHigh : reciprocalDepthBounds -> highHeightAsymptotic) :
    reciprocalDepthBounds ∧ highHeightAsymptotic := by
  exact ⟨hBounds, hHigh hBounds⟩

end Omega.Zeta
