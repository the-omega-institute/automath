import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete analytic data for transporting finite escort derivative identities to a limiting
pressure. -/
structure pom_pressure_derivatives_from_escort_data where
  finitePressure : ℕ → ℝ → ℝ
  limitPressure : ℝ → ℝ
  escortMean : ℕ → ℝ → ℝ
  escortVariance : ℕ → ℝ → ℝ
  limitingEscortMean : ℝ → ℝ
  limitingEscortVariance : ℝ → ℝ
  finite_first_identity :
    ∀ (n : ℕ) (q : ℝ), deriv (finitePressure n) q = escortMean n q
  finite_second_identity :
    ∀ (n : ℕ) (q : ℝ),
      deriv (fun x : ℝ => deriv (finitePressure n) x) q = escortVariance n q
  exchange_first :
    ∀ q : ℝ, deriv limitPressure q = limitingEscortMean q
  exchange_second :
    ∀ q : ℝ, deriv (fun x : ℝ => deriv limitPressure x) q = limitingEscortVariance q

namespace pom_pressure_derivatives_from_escort_data

/-- The finite escort formulas and the two limiting pressure derivative identities. -/
def derivative_identities (D : pom_pressure_derivatives_from_escort_data) : Prop :=
  (∀ (n : ℕ) (q : ℝ), deriv (D.finitePressure n) q = D.escortMean n q) ∧
    (∀ (n : ℕ) (q : ℝ),
      deriv (fun x : ℝ => deriv (D.finitePressure n) x) q = D.escortVariance n q) ∧
    (∀ q : ℝ,
      deriv D.limitPressure q = D.limitingEscortMean q ∧
        deriv (fun x : ℝ => deriv D.limitPressure x) q = D.limitingEscortVariance q)

end pom_pressure_derivatives_from_escort_data

/-- Paper label: `cor:pom-pressure-derivatives-from-escort`.  The finite pressure derivative
identities and the assumed limit/derivative exchanges give the limiting escort formulas for
`tau'` and `tau''`. -/
theorem paper_pom_pressure_derivatives_from_escort
    (D : pom_pressure_derivatives_from_escort_data) :
    D.derivative_identities := by
  refine ⟨D.finite_first_identity, D.finite_second_identity, ?_⟩
  intro q
  exact ⟨D.exchange_first q, D.exchange_second q⟩

end

end Omega.POM
