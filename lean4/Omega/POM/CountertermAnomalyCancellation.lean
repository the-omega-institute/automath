import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Relative anomaly after adding a finite-part counterterm. -/
def pom_counterterm_anom_cancel_relative_anomaly {n : ℕ}
    (anomaly counterterm : Fin n → ℝ) : Fin n → ℝ :=
  fun i => anomaly i + counterterm i

/-- Counterterm gate: it leaves the pole coordinates untouched and only shifts the finite drift. -/
def pom_counterterm_anom_cancel_counterterm_gate {n : ℕ}
    (pole finiteDrift counterterm : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (pole, fun i => finiteDrift i + counterterm i)

/-- A concrete pole-level observable used to record that the counterterm gate leaves the pole
data unchanged. -/
def pom_counterterm_anom_cancel_pole_mass {n : ℕ} (pole : Fin n → ℝ) : ℝ :=
  ∑ i, pole i

/-- Counterterm cancellation strictifies the anomaly square: inserting the negated anomaly kills
the relative anomaly, preserves the pole layer exactly, and only translates the finite drift.
    prop:pom-counterterm-anom-cancel -/
theorem paper_pom_counterterm_anom_cancel (n : ℕ)
    (pole finiteDrift anomaly : Fin n → ℝ) :
    let gate :=
      pom_counterterm_anom_cancel_counterterm_gate pole finiteDrift (fun i => -anomaly i)
    pom_counterterm_anom_cancel_relative_anomaly anomaly (fun i => -anomaly i) = 0 ∧
      gate.1 = pole ∧
      gate.2 = (fun i => finiteDrift i - anomaly i) ∧
      pom_counterterm_anom_cancel_pole_mass gate.1 = pom_counterterm_anom_cancel_pole_mass pole := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · ext i
    simp [pom_counterterm_anom_cancel_relative_anomaly]
  · ext i
    simp [pom_counterterm_anom_cancel_counterterm_gate, sub_eq_add_neg]

end Omega.POM
