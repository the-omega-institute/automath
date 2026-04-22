import Mathlib.Tactic

namespace Omega.POM

/-- A one-factor deleted polynomial used to witness the absorbing Wronskian identity. -/
def pom_diagonal_rate_absorbing_wronskian_identity_pMinus (a z : ℝ) : ℝ :=
  a - z

/-- The full polynomial obtained by restoring the deleted factor `(t_y - z)`. -/
def pom_diagonal_rate_absorbing_wronskian_identity_pDelta (ty a z : ℝ) : ℝ :=
  (ty - z) * pom_diagonal_rate_absorbing_wronskian_identity_pMinus a z

/-- The deleted Laguerre polynomial `Q_{-y}(z) = z P'_{-y}(z) + κ P_{-y}(z)` in the linear toy
model `P_{-y}(z) = a - z`. -/
def pom_diagonal_rate_absorbing_wronskian_identity_qMinus (κ a z : ℝ) : ℝ :=
  z * (-1) + κ * pom_diagonal_rate_absorbing_wronskian_identity_pMinus a z

/-- The full Laguerre polynomial `Q_δ(z) = z P'_δ(z) + κ P_δ(z)` for
`P_δ(z) = (t_y - z) P_{-y}(z)`. -/
def pom_diagonal_rate_absorbing_wronskian_identity_qDelta (κ ty a z : ℝ) : ℝ :=
  z * (2 * z - (ty + a)) + κ * pom_diagonal_rate_absorbing_wronskian_identity_pDelta ty a z

theorem pom_diagonal_rate_absorbing_wronskian_identity_polynomial (κ ty a z : ℝ) :
    (ty - z) ^ 2 * pom_diagonal_rate_absorbing_wronskian_identity_qMinus κ a z =
      (ty - z) * pom_diagonal_rate_absorbing_wronskian_identity_qDelta κ ty a z +
        z * pom_diagonal_rate_absorbing_wronskian_identity_pDelta ty a z := by
  unfold pom_diagonal_rate_absorbing_wronskian_identity_qMinus
    pom_diagonal_rate_absorbing_wronskian_identity_qDelta
    pom_diagonal_rate_absorbing_wronskian_identity_pDelta
    pom_diagonal_rate_absorbing_wronskian_identity_pMinus
  ring

/-- Paper label: `prop:pom-diagonal-rate-absorbing-wronskian-identity`. -/
theorem paper_pom_diagonal_rate_absorbing_wronskian_identity :
    ∀ κ ty a z : ℝ,
      (ty - z) ^ 2 * pom_diagonal_rate_absorbing_wronskian_identity_qMinus κ a z =
        (ty - z) * pom_diagonal_rate_absorbing_wronskian_identity_qDelta κ ty a z +
          z * pom_diagonal_rate_absorbing_wronskian_identity_pDelta ty a z := by
  intro κ ty a z
  exact pom_diagonal_rate_absorbing_wronskian_identity_polynomial κ ty a z

end Omega.POM
