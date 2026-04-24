import Mathlib.Tactic

namespace Omega.GroupUnification

/-- The two quadratic-sign values carried by the dual fingerprints. -/
inductive DualFingerprintQuadraticSign
  | neg
  | pos
  deriving DecidableEq

/-- The audited `S10`-side events. -/
inductive DualFingerprintS10Event
  | A
  | chi (ε : DualFingerprintQuadraticSign)
  deriving DecidableEq

/-- The audited `S3`-side events. -/
inductive DualFingerprintS3Event
  | B_split
  | B_root
  | chi (ε : DualFingerprintQuadraticSign)
  deriving DecidableEq

/-- Concrete density data for the dual-fingerprint Frobenius bookkeeping. The densities themselves
are explicit rational-valued observables on the two audited event families, together with the
product law and the audited marginals needed in the paper statement. -/
structure DualFingerprintFrobeniusConditionalDecouplingData where
  densityS10 : DualFingerprintS10Event → ℚ
  densityS3 : DualFingerprintS3Event → ℚ
  jointDensity : DualFingerprintS10Event → DualFingerprintS3Event → ℚ
  productDensity :
    ∀ E F, jointDensity E F = densityS10 E * densityS3 F
  densityA :
    densityS10 .A = 28319 / 33600
  densityBsplit :
    densityS3 .B_split = 1 / 8
  densityBroot :
    densityS3 .B_root = 1 / 2
  densityChi10 :
    ∀ ε, densityS10 (.chi ε) = 1 / 2
  densityChiLY :
    ∀ ε, densityS3 (.chi ε) = 1 / 2

/-- Product-density decoupling for the audited `A`, `B_split`, `B_root`, and quadratic-sign
events. The joint densities are the explicit rational values stated in the paper, and the
quadratic-sign layers are uniformly distributed on `{\pm 1}²`.
    thm:derived-dualfingerprint-frobenius-conditional-decoupling -/
def DualFingerprintFrobeniusConditionalDecoupling
    (D : DualFingerprintFrobeniusConditionalDecouplingData) : Prop :=
  D.jointDensity .A .B_split = 28319 / 268800 ∧
    D.jointDensity .A .B_root = 28319 / 67200 ∧
    (∀ ε₁ ε₂,
      D.jointDensity (.chi ε₁) (.chi ε₂) = 1 / 4) ∧
    (∀ ε, D.jointDensity (.chi ε) .B_split = D.densityS10 (.chi ε) * D.densityS3 .B_split) ∧
    (∀ ε, D.jointDensity .A (.chi ε) = D.densityS10 .A * D.densityS3 (.chi ε))

/-- Paper label:
`thm:derived-dualfingerprint-frobenius-conditional-decoupling`. -/
theorem paper_derived_dualfingerprint_frobenius_conditional_decoupling
    (D : DualFingerprintFrobeniusConditionalDecouplingData) :
    DualFingerprintFrobeniusConditionalDecoupling D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [D.productDensity, D.densityA, D.densityBsplit]
    norm_num
  · rw [D.productDensity, D.densityA, D.densityBroot]
    norm_num
  · intro ε₁ ε₂
    rw [D.productDensity, D.densityChi10, D.densityChiLY]
    norm_num
  · intro ε
    exact D.productDensity _ _
  · intro ε
    exact D.productDensity _ _

end Omega.GroupUnification
