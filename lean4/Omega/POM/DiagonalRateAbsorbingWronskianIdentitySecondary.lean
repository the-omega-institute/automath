import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingWronskianIdentity

namespace Omega.POM

/-- Concrete parameter package for the absorbing Wronskian identity. -/
structure DiagonalRateAbsorbingWronskianIdentitySecondaryData where
  κ : ℝ
  ty : ℝ
  a : ℝ
  z : ℝ

namespace DiagonalRateAbsorbingWronskianIdentitySecondaryData

/-- The secondary Wronskian identity evaluated at the concrete parameters carried by `D`. -/
def secondaryWronskianIdentity (D : DiagonalRateAbsorbingWronskianIdentitySecondaryData) : Prop :=
  (D.ty - D.z) ^ 2 * pom_diagonal_rate_absorbing_wronskian_identity_qMinus D.κ D.a D.z =
    (D.ty - D.z) * pom_diagonal_rate_absorbing_wronskian_identity_qDelta D.κ D.ty D.a D.z +
      D.z * pom_diagonal_rate_absorbing_wronskian_identity_pDelta D.ty D.a D.z

end DiagonalRateAbsorbingWronskianIdentitySecondaryData

open DiagonalRateAbsorbingWronskianIdentitySecondaryData

/-- Rewriting `Q_δ(z) = z P_δ'(z) + κ P_δ(z)` through `P_δ(z) = (t_y - z) P_{-y}(z)` produces the
intermediate identity used in the paper proof. -/
theorem pom_diagonal_rate_absorbing_wronskian_identity_secondary_qDelta_rewrite
    (κ ty a z : ℝ) :
    pom_diagonal_rate_absorbing_wronskian_identity_qDelta κ ty a z =
      -z * pom_diagonal_rate_absorbing_wronskian_identity_pMinus a z +
        (ty - z) * pom_diagonal_rate_absorbing_wronskian_identity_qMinus κ a z := by
  unfold pom_diagonal_rate_absorbing_wronskian_identity_qDelta
    pom_diagonal_rate_absorbing_wronskian_identity_qMinus
    pom_diagonal_rate_absorbing_wronskian_identity_pDelta
    pom_diagonal_rate_absorbing_wronskian_identity_pMinus
  ring

/-- Paper label: `prop:pom-diagonal-rate-absorbing-wronskian-identity-secondary`. Expanding
`P_δ = (t_y - z) P_{-y}`, differentiating, and rewriting the resulting `Q_δ` term yields the
secondary Wronskian identity. -/
theorem paper_pom_diagonal_rate_absorbing_wronskian_identity_secondary
    (D : DiagonalRateAbsorbingWronskianIdentitySecondaryData) : D.secondaryWronskianIdentity := by
  dsimp [DiagonalRateAbsorbingWronskianIdentitySecondaryData.secondaryWronskianIdentity]
  rw [pom_diagonal_rate_absorbing_wronskian_identity_secondary_qDelta_rewrite]
  unfold pom_diagonal_rate_absorbing_wronskian_identity_pDelta
    pom_diagonal_rate_absorbing_wronskian_identity_pMinus
  ring

end Omega.POM
