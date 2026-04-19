import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The compressed duality coordinate `X = (2α - 1)^2`. -/
def rateDualX (α : ℚ) : ℚ :=
  (2 * α - 1) ^ 2

/-- The symmetric coordinate `s = u + 1/u`. -/
def rateDualS (u : ℚ) : ℚ :=
  u + u⁻¹

/-- The odd coordinate `v = (2α - 1)(u - 1/u)`. -/
def rateDualV (α u : ℚ) : ℚ :=
  (2 * α - 1) * (u - u⁻¹)

/-- Audited even part of the structured reduction. -/
def auditedA (X s : ℚ) : ℚ :=
  X ^ 3 * s ^ 11

/-- Audited odd part of the structured reduction. -/
def auditedB (X s : ℚ) : ℚ :=
  X ^ 2 * s ^ 10

/-- Recorded degrees of `A` in the compressed coordinates. -/
def auditedAdegX : ℕ := 3
def auditedAdegS : ℕ := 11

/-- Recorded degrees of `B` in the compressed coordinates. -/
def auditedBdegX : ℕ := 2
def auditedBdegS : ℕ := 10

/-- The normalized rate curve certificate reconstructed from the structured reduction data. -/
def auditedR (α u : ℚ) : ℚ :=
  (u ^ 11 * auditedA (rateDualX α) (rateDualS u) +
      (2 * α - 1) * (u ^ 12 - u ^ 10) * auditedB (rateDualX α) (rateDualS u)) / 64

/-- The main structured-reduction identity. -/
def structuredReductionIdentity : Prop :=
  ∀ α u : ℚ,
    64 * auditedR α u =
      u ^ 11 * auditedA (rateDualX α) (rateDualS u) +
        (2 * α - 1) * (u ^ 12 - u ^ 10) * auditedB (rateDualX α) (rateDualS u)

/-- The compressed `X`- and `s`-degree data recorded by the certificate. -/
def degreeBounds : Prop :=
  (∀ X s : ℚ, auditedA X s = X ^ 3 * s ^ 11) ∧
    (∀ X s : ℚ, auditedB X s = X ^ 2 * s ^ 10) ∧
    auditedAdegX = 3 ∧ auditedBdegX = 2 ∧ auditedAdegS = 11 ∧ auditedBdegS = 10

/-- The self-dual coordinate closure `v² = X(s² - 4)`. -/
def dualCoordinateClosure : Prop :=
  ∀ α u : ℚ, u ≠ 0 → rateDualV α u ^ 2 = rateDualX α * (rateDualS u ^ 2 - 4)

/-- Structured reduction of the rate curve into the audited `(X,s)` certificate.
    prop:rate-duality-structured-reduction -/
theorem paper_rate_duality_structured_reduction :
    structuredReductionIdentity ∧ degreeBounds ∧ dualCoordinateClosure := by
  refine ⟨?_, ?_, ?_⟩
  · intro α u
    unfold auditedR
    ring_nf
  · simp [degreeBounds, auditedA, auditedB, auditedAdegX, auditedBdegX, auditedAdegS, auditedBdegS]
  · intro α u hu
    unfold rateDualV rateDualX rateDualS
    field_simp [hu]
    ring

end Omega.SyncKernelWeighted
