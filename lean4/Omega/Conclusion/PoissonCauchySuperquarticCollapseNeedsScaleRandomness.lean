import Mathlib.Tactic

namespace Omega.Conclusion

/-- The quartic invariant controlling the superquartic collapse. -/
def conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_quarticInvariant
    (sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) : ℝ :=
  (sigmaGamma2 - sigmaDelta2) ^ 2 + (2 * sigmaGammaDelta) ^ 2

/-- Conclusion wrapper for superquartic collapse in the Poisson/Cauchy model: once the quartic
invariant vanishes, the two variances coincide, the covariance is zero, and a short case split
shows that the collapse is either the pure-translation case or a genuinely nondegenerate balanced
scale-randomness regime. -/
def conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_statement : Prop :=
  ∀ sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ,
    let conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_superquarticCollapse :
        Prop :=
      conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_quarticInvariant
        sigmaGamma2 sigmaDelta2 sigmaGammaDelta = 0
    conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_superquarticCollapse →
      sigmaGamma2 = sigmaDelta2 ∧
        sigmaGammaDelta = 0 ∧
        ((sigmaGamma2 = 0 ∧ sigmaDelta2 = 0) ∨
          (sigmaGamma2 ≠ 0 ∧ sigmaDelta2 ≠ 0))

/-- Paper label:
`thm:conclusion-poisson-cauchy-superquartic-collapse-needs-scale-randomness`. -/
theorem paper_conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness :
    conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_statement := by
  intro sigmaGamma2 sigmaDelta2 sigmaGammaDelta
  dsimp
  intro hCollapse
  have hSum :
      (sigmaGamma2 - sigmaDelta2) ^ 2 + (2 * sigmaGammaDelta) ^ 2 = 0 := by
    simpa [conclusion_poisson_cauchy_superquartic_collapse_needs_scale_randomness_quarticInvariant]
      using hCollapse
  have hVarSq : (sigmaGamma2 - sigmaDelta2) ^ 2 = 0 := by
    have hle :
        (sigmaGamma2 - sigmaDelta2) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (2 * sigmaGammaDelta), hSum]
    exact le_antisymm hle (sq_nonneg _)
  have hCovSq : sigmaGammaDelta ^ 2 = 0 := by
    have hTwoCovSq : (2 * sigmaGammaDelta) ^ 2 = 0 := by
      have hle : (2 * sigmaGammaDelta) ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (sigmaGamma2 - sigmaDelta2), hSum]
      exact le_antisymm hle (sq_nonneg _)
    nlinarith
  have hVar : sigmaGamma2 - sigmaDelta2 = 0 := by
    nlinarith
  have hCov : sigmaGammaDelta = 0 := by
    nlinarith
  have hEq : sigmaGamma2 = sigmaDelta2 := by
    linarith
  refine ⟨hEq, hCov, ?_⟩
  by_cases hZero : sigmaGamma2 = 0
  · left
    constructor
    · exact hZero
    · linarith
  · right
    constructor
    · exact hZero
    · intro hDeltaZero
      apply hZero
      linarith

end Omega.Conclusion
