namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-nearest-conjugate-pair-discriminant-estimator`. -/
theorem paper_xi_leyang_nearest_conjugate_pair_discriminant_estimator
    (dominantGap conjugatePair hankelDiscriminantNonzero quadraticEstimator
      exponentialZetaRecovery : Prop)
    (hPair : dominantGap → conjugatePair)
    (hDisc : conjugatePair → hankelDiscriminantNonzero)
    (hEstimator : hankelDiscriminantNonzero → quadraticEstimator)
    (hRecovery : quadraticEstimator → exponentialZetaRecovery) :
    dominantGap →
      conjugatePair ∧ hankelDiscriminantNonzero ∧ quadraticEstimator ∧ exponentialZetaRecovery := by
  intro hDominant
  have hConjugate : conjugatePair := hPair hDominant
  have hDiscriminant : hankelDiscriminantNonzero := hDisc hConjugate
  have hQuadratic : quadraticEstimator := hEstimator hDiscriminant
  exact ⟨hConjugate, hDiscriminant, hQuadratic, hRecovery hQuadratic⟩

end Omega.Zeta
