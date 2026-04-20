import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete certificate data for the weighted Newman threshold package. -/
structure WeightedNewmanThresholdData where
  uStar : ℚ
  threshold : ℚ
  residualSlope : ℚ
  residualIntercept : ℚ

/-- The linear residual factor that survives after eliminating the weighted kernel variable. -/
def weightedNewmanResidual (D : WeightedNewmanThresholdData) (u : ℚ) : ℚ :=
  D.residualSlope * u + D.residualIntercept

/-- The eliminated polynomial `Q` with a distinguished double root at `u⋆`. -/
def weightedNewmanEliminatedPolynomial (D : WeightedNewmanThresholdData) (u : ℚ) : ℚ :=
  (u - D.uStar) ^ 2 * weightedNewmanResidual D u

/-- Audited spectral gap relative to the threshold parameter. -/
def weightedNewmanSpectralGap (D : WeightedNewmanThresholdData) (t : ℚ) : ℚ :=
  D.threshold - t

/-- The eliminated polynomial factors through the distinguished square factor. -/
def WeightedNewmanThresholdData.resultantFactorization (D : WeightedNewmanThresholdData) : Prop :=
  ∀ u, weightedNewmanEliminatedPolynomial D u =
    (u - D.uStar) ^ 2 * weightedNewmanResidual D u

/-- The only critical root that survives once the residual factor is nonzero is `u⋆`. -/
def WeightedNewmanThresholdData.uniqueCriticalRoot (D : WeightedNewmanThresholdData) : Prop :=
  weightedNewmanEliminatedPolynomial D D.uStar = 0 ∧
    ∀ u,
      weightedNewmanEliminatedPolynomial D u = 0 →
        weightedNewmanResidual D u ≠ 0 → u = D.uStar

/-- The audited spectral comparison stays positive below the threshold. -/
def WeightedNewmanThresholdData.rhStrictBelowThreshold (D : WeightedNewmanThresholdData) : Prop :=
  ∀ t, t < D.threshold → 0 < weightedNewmanSpectralGap D t

/-- The spectral comparison is sharp exactly at the threshold. -/
def WeightedNewmanThresholdData.rhSharpAtThreshold (D : WeightedNewmanThresholdData) : Prop :=
  weightedNewmanSpectralGap D D.threshold = 0

/-- The RH comparison fails above the threshold. -/
def WeightedNewmanThresholdData.rhFailsAboveThreshold (D : WeightedNewmanThresholdData) : Prop :=
  ∀ t, D.threshold < t → weightedNewmanSpectralGap D t < 0

/-- Paper-facing threshold trichotomy for the weighted Newman certificate.
    prop:sync-kernel-weighted-newman-threshold -/
theorem paper_sync_kernel_weighted_newman_threshold (D : WeightedNewmanThresholdData) :
    D.resultantFactorization ∧ D.uniqueCriticalRoot ∧ D.rhStrictBelowThreshold ∧
      D.rhSharpAtThreshold ∧ D.rhFailsAboveThreshold := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rfl
  · refine ⟨?_, ?_⟩
    · simp [weightedNewmanEliminatedPolynomial]
    · intro u hQ hres
      have hsq : (u - D.uStar) ^ 2 = 0 := by
        have hprod : (u - D.uStar) ^ 2 * weightedNewmanResidual D u = 0 := by
          simpa [weightedNewmanEliminatedPolynomial] using hQ
        exact Or.resolve_right (mul_eq_zero.mp hprod) hres
      have hsub : u - D.uStar = 0 := by
        nlinarith [sq_nonneg (u - D.uStar), hsq]
      linarith
  · intro t ht
    dsimp [weightedNewmanSpectralGap]
    linarith
  · simp [WeightedNewmanThresholdData.rhSharpAtThreshold, weightedNewmanSpectralGap]
  · intro t ht
    dsimp [weightedNewmanSpectralGap]
    linarith

end Omega.SyncKernelWeighted
