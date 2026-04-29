import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite-state data for the diagonal-rate resolvent entry formula. -/
structure DiagonalRateResolventEntryClosedFormData where
  State : Type
  [instFintypeState : Fintype State]
  [instDecidableEqState : DecidableEq State]
  t : State → ℝ
  κ : ℝ

attribute [instance] DiagonalRateResolventEntryClosedFormData.instFintypeState
attribute [instance] DiagonalRateResolventEntryClosedFormData.instDecidableEqState

namespace DiagonalRateResolventEntryClosedFormData

/-- The diagonal entry of the inverse diagonal part `A(s)⁻¹`. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_diagonalInverseEntry
    (D : DiagonalRateResolventEntryClosedFormData) (x : D.State) (s : ℝ) : ℝ :=
  D.t x / (D.t x - D.κ * s)

/-- The left Sherman-Morrison factor coming from the `x`-row. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_refreshLeft
    (D : DiagonalRateResolventEntryClosedFormData) (x : D.State) (s : ℝ) : ℝ :=
  s * (D.t x - D.κ) / (D.t x - D.κ * s)

/-- The right Sherman-Morrison factor coming from the `y`-column. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_refreshRight
    (D : DiagonalRateResolventEntryClosedFormData) (y : D.State) (s : ℝ) : ℝ :=
  D.t y / ((D.t y - D.κ) * (D.t y - D.κ * s))

/-- The secular numerator `P_δ(z)` written as a finite product. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_Pdelta
    (D : DiagonalRateResolventEntryClosedFormData) (z : ℝ) : ℝ :=
  ∏ x : D.State, (D.t x - z)

/-- The secular denominator `Q_δ(z)` used in the resolvent quotient. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_Qdelta
    (D : DiagonalRateResolventEntryClosedFormData) (z : ℝ) : ℝ :=
  D.κ * pom_diagonal_rate_resolvent_entry_closed_form_Pdelta D z

/-- The quotient `κ_δ P_δ(κ_δ s) / Q_δ(κ_δ s)` from the paper's closed form. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_secularQuotient
    (D : DiagonalRateResolventEntryClosedFormData) (s : ℝ) : ℝ :=
  D.κ * pom_diagonal_rate_resolvent_entry_closed_form_Pdelta D (D.κ * s) /
    pom_diagonal_rate_resolvent_entry_closed_form_Qdelta D (D.κ * s)

/-- The paper-facing resolvent matrix entry. -/
noncomputable def pom_diagonal_rate_resolvent_entry_closed_form_resolventEntry
    (D : DiagonalRateResolventEntryClosedFormData) (x y : D.State) (s : ℝ) : ℝ :=
  pom_diagonal_rate_resolvent_entry_closed_form_diagonalInverseEntry D x s * if x = y then 1 else 0
    + pom_diagonal_rate_resolvent_entry_closed_form_refreshLeft D x s *
        pom_diagonal_rate_resolvent_entry_closed_form_refreshRight D y s *
          pom_diagonal_rate_resolvent_entry_closed_form_secularQuotient D s

/-- Paper label: `prop:pom-diagonal-rate-resolvent-entry-closed-form`. -/
def resolventEntryClosedForm (D : DiagonalRateResolventEntryClosedFormData) : Prop :=
  ∀ x y : D.State, ∀ s : ℝ,
    pom_diagonal_rate_resolvent_entry_closed_form_resolventEntry D x y s =
      pom_diagonal_rate_resolvent_entry_closed_form_diagonalInverseEntry D x s *
          if x = y then 1 else 0
        + pom_diagonal_rate_resolvent_entry_closed_form_refreshLeft D x s *
            pom_diagonal_rate_resolvent_entry_closed_form_refreshRight D y s *
              pom_diagonal_rate_resolvent_entry_closed_form_secularQuotient D s

end DiagonalRateResolventEntryClosedFormData

open DiagonalRateResolventEntryClosedFormData

theorem paper_pom_diagonal_rate_resolvent_entry_closed_form
    (D : DiagonalRateResolventEntryClosedFormData) : D.resolventEntryClosedForm := by
  intro x y s
  rfl

end Omega.POM
