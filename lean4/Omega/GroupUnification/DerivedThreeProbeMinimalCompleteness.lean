import Mathlib.Tactic
import Omega.GroupUnification.DerivedDualfingerprintFrobeniusConditionalDecoupling

namespace Omega.GroupUnification

/-- Explicit audited `S10` marginal used in the minimal-completeness corollary. -/
def derivedThreeProbeDensityS10 : DualFingerprintS10Event → ℚ
  | .A => 28319 / 33600
  | .chi _ => 1 / 2

/-- Explicit audited `S3` marginal used in the minimal-completeness corollary. -/
def derivedThreeProbeDensityS3 : DualFingerprintS3Event → ℚ
  | .B_split => 1 / 8
  | .B_root => 1 / 2
  | .chi _ => 1 / 2

/-- Explicit audited product-density model used to read off the asymptotic quadrant law. -/
def derivedThreeProbeMinimalCompletenessData : DualFingerprintFrobeniusConditionalDecouplingData where
  densityS10 := derivedThreeProbeDensityS10
  densityS3 := derivedThreeProbeDensityS3
  jointDensity E F := derivedThreeProbeDensityS10 E * derivedThreeProbeDensityS3 F
  productDensity := by
    intro E F
    rfl
  densityA := by rfl
  densityBsplit := by rfl
  densityBroot := by rfl
  densityChi10 := by
    intro ε
    rfl
  densityChiLY := by
    intro ε
    rfl

/-- Variance in the first probe direction. -/
def derivedThreeProbeVariance₁ (M11 _M12 _M22 : ℚ) : ℚ := M11

/-- Variance in the second probe direction. -/
def derivedThreeProbeVariance₂ (_M11 _M12 M22 : ℚ) : ℚ := M22

/-- Variance in the third probe direction `e₁ + e₂`. -/
def derivedThreeProbeVariance₃ (M11 M12 M22 : ℚ) : ℚ := M11 + 2 * M12 + M22

/-- Recovery formula for the off-diagonal entry from the three probe variances. -/
def derivedThreeProbeRecoverOffDiagonal (v1 v2 v3 : ℚ) : ℚ := (v3 - v1 - v2) / 2

/-- Two-probe data only records the diagonal directional variances. -/
def derivedTwoProbeSignature (M11 M12 M22 : ℚ) : ℚ × ℚ :=
  (derivedThreeProbeVariance₁ M11 M12 M22, derivedThreeProbeVariance₂ M11 M12 M22)

/-- Paper label: `cor:derived-three-probe-minimal-completeness`. The audited dual-fingerprint
decoupling gives the asymptotic `1/4` quadrant law, three probe variances recover the mixed term
exactly, and any two-probe audit leaves the off-diagonal entry undetermined. -/
theorem paper_derived_three_probe_minimal_completeness (M11 M12 M22 : ℚ) :
    derivedThreeProbeMinimalCompletenessData.jointDensity (.chi .neg) (.chi .neg) = 1 / 4 ∧
      derivedThreeProbeMinimalCompletenessData.jointDensity (.chi .neg) (.chi .pos) = 1 / 4 ∧
      derivedThreeProbeMinimalCompletenessData.jointDensity (.chi .pos) (.chi .neg) = 1 / 4 ∧
      derivedThreeProbeMinimalCompletenessData.jointDensity (.chi .pos) (.chi .pos) = 1 / 4 ∧
      derivedThreeProbeRecoverOffDiagonal
          (derivedThreeProbeVariance₁ M11 M12 M22)
          (derivedThreeProbeVariance₂ M11 M12 M22)
          (derivedThreeProbeVariance₃ M11 M12 M22) = M12 ∧
      ∃ M12' : ℚ,
        M12' ≠ M12 ∧
          derivedTwoProbeSignature M11 M12' M22 = derivedTwoProbeSignature M11 M12 M22 := by
  have hDecouple :
      DualFingerprintFrobeniusConditionalDecoupling derivedThreeProbeMinimalCompletenessData := by
    exact paper_derived_dualfingerprint_frobenius_conditional_decoupling
      derivedThreeProbeMinimalCompletenessData
  rcases hDecouple with ⟨_, _, hQuadrant, _, _⟩
  refine ⟨hQuadrant .neg .neg, hQuadrant .neg .pos, hQuadrant .pos .neg, hQuadrant .pos .pos,
    ?_, ?_⟩
  · unfold derivedThreeProbeRecoverOffDiagonal derivedThreeProbeVariance₁
      derivedThreeProbeVariance₂ derivedThreeProbeVariance₃
    ring
  · refine ⟨M12 + 1, by linarith, ?_⟩
    unfold derivedTwoProbeSignature derivedThreeProbeVariance₁ derivedThreeProbeVariance₂
    rfl

end Omega.GroupUnification
