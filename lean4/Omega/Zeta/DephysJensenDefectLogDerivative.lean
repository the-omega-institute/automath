import Omega.UnitCirclePhaseArithmetic.AppJensenDefectLogDerivative

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete dephysicalized Jensen-defect data: a finite disk-zero model with all listed roots
away from the origin. -/
structure dephys_jensen_defect_log_derivative_data where
  roots : Finset ℂ
  root_pos : ∀ z ∈ roots, 0 < ‖z‖

/-- The finite Jensen defect attached to the dephysicalized data. -/
def dephys_jensen_defect_log_derivative_data.defect
    (D : dephys_jensen_defect_log_derivative_data) (ρ : ℝ) : ℝ :=
  Omega.UnitCirclePhaseArithmetic.appSingleZeroJensenDefect ρ D.roots

/-- The zero-counting function attached to the dephysicalized data. -/
def dephys_jensen_defect_log_derivative_data.zeroCount
    (D : dephys_jensen_defect_log_derivative_data) (ρ : ℝ) : ℕ :=
  Omega.UnitCirclePhaseArithmetic.appJensenZeroCount D.roots ρ

/-- Publication-facing dephysicalized Jensen package: the logarithmic-radius derivative is the
zero count away from shell radii, and the finite Jensen defect is continuous, monotone, and has
hereditary vanishing toward smaller radii. -/
def dephys_jensen_defect_log_derivative_data.dephys_jensen_defect_log_derivative_statement
    (D : dephys_jensen_defect_log_derivative_data) : Prop :=
  (∀ {t : ℝ}, (∀ z ∈ D.roots, ‖z‖ ≠ Real.exp t) →
      HasDerivAt (fun s => D.defect (Real.exp s)) (D.zeroCount (Real.exp t)) t) ∧
    Continuous (fun t => D.defect (Real.exp t)) ∧
    Monotone (fun t => D.defect (Real.exp t)) ∧
    (∀ {t t₀ : ℝ}, t ≤ t₀ → D.defect (Real.exp t₀) = 0 →
      D.defect (Real.exp t) = 0)

/-- Paper label: `prop:dephys-jensen-defect-log-derivative`. -/
theorem paper_dephys_jensen_defect_log_derivative
    (D : dephys_jensen_defect_log_derivative_data) :
    D.dephys_jensen_defect_log_derivative_statement := by
  simpa [dephys_jensen_defect_log_derivative_data.dephys_jensen_defect_log_derivative_statement,
    dephys_jensen_defect_log_derivative_data.defect,
    dephys_jensen_defect_log_derivative_data.zeroCount] using
    Omega.UnitCirclePhaseArithmetic.paper_app_jensen_defect_log_derivative D.roots D.root_pos

end

end Omega.Zeta
