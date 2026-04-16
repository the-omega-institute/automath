namespace Omega.GU

/-- Paper-facing wrapper for the rational commutant product decomposition, idempotent
classification, and rational spectral projection consequences for terminal window pushforwards.
    thm:terminal-windowm-rational-commutant-idempotent-rigidity -/
theorem paper_terminal_windowm_rational_commutant_idempotent_rigidity
    (commutantProduct idempotentClassification rationalProjection : Prop)
    (hProduct : commutantProduct)
    (hIdempotents : commutantProduct -> idempotentClassification)
    (hProjection : commutantProduct -> rationalProjection) :
    commutantProduct ∧ idempotentClassification ∧ rationalProjection := by
  have hIdempotentClassification : idempotentClassification := hIdempotents hProduct
  have hRationalProjection : rationalProjection := hProjection hProduct
  exact ⟨hProduct, hIdempotentClassification, hRationalProjection⟩

end Omega.GU
