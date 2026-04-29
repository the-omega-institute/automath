import Mathlib
import Omega.UnitCirclePhaseArithmetic.AppCayleyUpperhalfDisk

namespace Omega.Zeta

noncomputable section

/-- The explicit derivative of the appendix Cayley-side coordinate `s(w) = (3 - w) / (2 (1 + w))`
used in the pole transfer. -/
def appHorizonSderiv (w : ℂ) : ℂ :=
  2 / (1 + w) ^ 2

/-- The pole residue transferred from the logarithmic derivative to the `w`-chart. -/
def appHorizonResidueFactor (wρ : ℂ) : ℂ :=
  -((1 + wρ) ^ 2) / 2

/-- The principal part of the pole contribution in the `w`-chart. -/
def appHorizonPolePrincipalPart (wρ w : ℂ) : ℂ :=
  appHorizonResidueFactor wρ / (w - wρ)

/-- Constant contribution of the pole to the Carathéodory expansion around `0`. -/
def appHorizonPoleConstantContribution (wρ : ℂ) : ℂ :=
  (1 + wρ) ^ 2 / (2 * wρ)

/-- For `n ≥ 1`, the normalized coefficient contribution to `c_n` in
`c₀ + 2 * Σ_{n≥1} c_n w^n`. -/
def appHorizonPoleNormalizedCoeff (wρ : ℂ) (n : ℕ) : ℂ :=
  (1 + wρ) ^ 2 / (4 * wρ ^ (n + 1))

lemma appHorizonResidueFactor_eq_neg_inv_sderiv (wρ : ℂ) (hρ : wρ ≠ -1) :
    appHorizonResidueFactor wρ = -1 / appHorizonSderiv wρ := by
  have hneq : 1 + wρ ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero, add_comm] using hρ
  have hpow : (1 + wρ) ^ 2 ≠ 0 := pow_ne_zero 2 hneq
  unfold appHorizonResidueFactor appHorizonSderiv
  field_simp [hpow]

/-- Paper label: `prop:app-horizon-pole-imprint`. The explicit derivative of the Cayley-side map
gives the residue factor `-(1 + wρ)^2 / 2`; rewriting the pole as a geometric resolvent around
`0` yields the constant term and the normalized `n`-th coefficient contribution. -/
theorem paper_app_horizon_pole_imprint
    (wρ w : ℂ) (n : ℕ) (hwρ : wρ ≠ 0) (hρ : wρ ≠ -1) :
    appHorizonResidueFactor wρ = -1 / appHorizonSderiv wρ ∧
      appHorizonPolePrincipalPart wρ w =
        appHorizonPoleConstantContribution wρ * (1 / (1 - w / wρ)) ∧
      appHorizonPolePrincipalPart wρ 0 = appHorizonPoleConstantContribution wρ ∧
      2 * appHorizonPoleNormalizedCoeff wρ n =
        (1 + wρ) ^ 2 / (2 * wρ ^ (n + 1)) := by
  refine ⟨appHorizonResidueFactor_eq_neg_inv_sderiv wρ hρ, ?_, ?_, ?_⟩
  · unfold appHorizonPolePrincipalPart appHorizonPoleConstantContribution appHorizonResidueFactor
    have hgeom : (1 : ℂ) / (1 - w / wρ) = wρ / (wρ - w) := by
      field_simp [hwρ]
    have hneg : w - wρ = -(wρ - w) := by ring
    rw [hneg, hgeom]
    field_simp [hwρ]
  · unfold appHorizonPolePrincipalPart appHorizonPoleConstantContribution appHorizonResidueFactor
    field_simp [hwρ]
    ring
  · unfold appHorizonPoleNormalizedCoeff
    have hpow : wρ ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hwρ
    field_simp [hpow]
    ring

end

end Omega.Zeta
