import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete microreversible pressure data for the critical-slice package. The pressure profile is
even, the central pressure vanishes, the Lyapunov witness is read from the central value, and the
only double-zero slice is the central slice `0`. -/
structure xi_critical_slice_pressure_zero_drift_lyapunov_data where
  pressure : ℝ → ℝ
  lyapunovWitness : ℝ
  pressure_even : Function.Even pressure
  central_zero : pressure 0 = 0
  lyapunov_eq_center : lyapunovWitness = pressure 0
  microreversibility : ∀ s : ℝ, pressure s = 0 → pressure (-s) = 0 → s = 0

/-- The central drift is the antisymmetric defect of the pressure at the critical slice. -/
def xi_critical_slice_pressure_zero_drift_lyapunov_drift
    (D : xi_critical_slice_pressure_zero_drift_lyapunov_data) : ℝ :=
  D.pressure 0 - D.pressure (-0)

/-- A slice is a double-zero slice when both it and its time-reversed partner carry zero pressure.
-/
def xi_critical_slice_pressure_zero_drift_lyapunov_double_zero
    (D : xi_critical_slice_pressure_zero_drift_lyapunov_data) (s : ℝ) : Prop :=
  D.pressure s = 0 ∧ D.pressure (-s) = 0

/-- Every microreversible even pressure family has zero pressure, zero drift, and zero Lyapunov
witness on the critical slice, and the critical slice is the unique double-zero slice. -/
def xi_critical_slice_pressure_zero_drift_lyapunov_statement : Prop :=
  ∀ D : xi_critical_slice_pressure_zero_drift_lyapunov_data,
    D.pressure 0 = 0 ∧
      xi_critical_slice_pressure_zero_drift_lyapunov_drift D = 0 ∧
      D.lyapunovWitness = 0 ∧
      xi_critical_slice_pressure_zero_drift_lyapunov_double_zero D 0 ∧
      ∀ s : ℝ, xi_critical_slice_pressure_zero_drift_lyapunov_double_zero D s → s = 0

/-- Paper label: `thm:xi-critical-slice-pressure-zero-drift-lyapunov`. Evenness forces zero drift
at the central slice, the Lyapunov witness collapses to the central pressure, and
microreversibility makes the central slice the unique double-zero slice. -/
theorem paper_xi_critical_slice_pressure_zero_drift_lyapunov :
    xi_critical_slice_pressure_zero_drift_lyapunov_statement := by
  intro D
  refine ⟨D.central_zero, ?_, ?_, ?_, ?_⟩
  · dsimp [xi_critical_slice_pressure_zero_drift_lyapunov_drift]
    simp
  · rw [D.lyapunov_eq_center, D.central_zero]
  · constructor <;> simpa using D.central_zero
  · intro s hs
    exact D.microreversibility s hs.1 hs.2

end Omega.Zeta
