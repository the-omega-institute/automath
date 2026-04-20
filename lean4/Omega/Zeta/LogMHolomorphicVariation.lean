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

/-- Chapter-local package for the explicit truncation bound on `log M`. The data record the
eigenvalue-factorized expansion of `log ζ`, the standard `|log (1 - w)|` estimate at
`w = λⱼ * λ⁻ᵏ`, the comparison with the geometric-harmonic tail, the `1 / (K + 1)` cutoff, and
the final explicit truncation inequality. -/
structure FinitePartLogMTruncationExplicitBoundData where
  logZetaEigenvalueFactorization : Prop
  logOneSubBoundAtInversePowers : Prop
  truncationTailComparison : Prop
  geometricTailWithCutoff : Prop
  explicitTruncationBound : Prop
  logZetaEigenvalueFactorization_h : logZetaEigenvalueFactorization
  deriveLogOneSubBoundAtInversePowers :
    logZetaEigenvalueFactorization → logOneSubBoundAtInversePowers
  deriveTruncationTailComparison :
    logZetaEigenvalueFactorization → logOneSubBoundAtInversePowers → truncationTailComparison
  deriveGeometricTailWithCutoff :
    truncationTailComparison → geometricTailWithCutoff
  deriveExplicitTruncationBound :
    logZetaEigenvalueFactorization → logOneSubBoundAtInversePowers →
      truncationTailComparison → geometricTailWithCutoff → explicitTruncationBound

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the explicit truncation bound on `log M`: expand
`log ζ(λ⁻ᵏ)` through the eigenvalue factorization, bound each logarithm by
`|w| / (1 - |w|)`, compare the tail with a geometric-harmonic series, and sum it with the
`1 / (K + 1)` cutoff.
    thm:finite-part-logM-truncation-explicit-bound -/
theorem paper_finite_part_logM_truncation_explicit_bound
    (D : FinitePartLogMTruncationExplicitBoundData) :
    D.logZetaEigenvalueFactorization ∧
      D.logOneSubBoundAtInversePowers ∧
      D.truncationTailComparison ∧
      D.geometricTailWithCutoff ∧
      D.explicitTruncationBound := by
  have hLogBound : D.logOneSubBoundAtInversePowers :=
    D.deriveLogOneSubBoundAtInversePowers D.logZetaEigenvalueFactorization_h
  have hTailComparison : D.truncationTailComparison :=
    D.deriveTruncationTailComparison D.logZetaEigenvalueFactorization_h hLogBound
  have hGeometricTail : D.geometricTailWithCutoff :=
    D.deriveGeometricTailWithCutoff hTailComparison
  exact ⟨D.logZetaEigenvalueFactorization_h, hLogBound, hTailComparison, hGeometricTail,
    D.deriveExplicitTruncationBound D.logZetaEigenvalueFactorization_h hLogBound
      hTailComparison hGeometricTail⟩

set_option maxHeartbeats 400000 in
/-- Chapter-local wrapper packaging termwise holomorphicity of the `log M` series with the
    log-zeta trace-derivative identity.
    thm:finite-part-logM-holomorphic-variation -/
theorem paper_finite_part_logM_holomorphic_variation
    (termwiseDifferentiation logZetaTraceDerivative holomorphicVariation : Prop)
    (hTermwise : termwiseDifferentiation)
    (hTrace : logZetaTraceDerivative)
    (hHolomorphic :
      termwiseDifferentiation → logZetaTraceDerivative → holomorphicVariation) :
    termwiseDifferentiation ∧ logZetaTraceDerivative ∧ holomorphicVariation := by
  exact ⟨hTermwise, hTrace, hHolomorphic hTermwise hTrace⟩

end Omega.Zeta
