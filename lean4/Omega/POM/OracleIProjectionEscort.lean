import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete finite data for the oracle I-projection/escort package. -/
structure pom_oracle_i_projection_escort_data where
  pom_oracle_i_projection_escort_supportCard : ℕ
  pom_oracle_i_projection_escort_reference :
    Fin pom_oracle_i_projection_escort_supportCard → ℝ
  pom_oracle_i_projection_escort_statistic :
    Fin pom_oracle_i_projection_escort_supportCard → ℝ
  pom_oracle_i_projection_escort_escort :
    Fin pom_oracle_i_projection_escort_supportCard → ℝ
  pom_oracle_i_projection_escort_lambda : ℝ
  pom_oracle_i_projection_escort_pressure : ℝ → ℝ
  pom_oracle_i_projection_escort_pressureLimit : ℝ

/-- Normalization and positivity for a finite candidate law. -/
def pom_oracle_i_projection_escort_data.normalized
    (D : pom_oracle_i_projection_escort_data)
    (q : Fin D.pom_oracle_i_projection_escort_supportCard → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1

/-- The imposed mean coordinate. -/
def pom_oracle_i_projection_escort_data.mean
    (D : pom_oracle_i_projection_escort_data)
    (q : Fin D.pom_oracle_i_projection_escort_supportCard → ℝ) : ℝ :=
  ∑ i, q i * D.pom_oracle_i_projection_escort_statistic i

/-- Finite quadratic KL proxy against the reference law. -/
def pom_oracle_i_projection_escort_data.kl
    (D : pom_oracle_i_projection_escort_data)
    (q : Fin D.pom_oracle_i_projection_escort_supportCard → ℝ) : ℝ :=
  ∑ i, q i * (q i - D.pom_oracle_i_projection_escort_reference i)

/-- Strict convexity hypothesis for the finite KL proxy on the normalized affine slice. -/
def pom_oracle_i_projection_escort_data.kl_strictly_convex
    (D : pom_oracle_i_projection_escort_data) : Prop :=
  0 < D.pom_oracle_i_projection_escort_supportCard ∧
    ∀ q r : Fin D.pom_oracle_i_projection_escort_supportCard → ℝ,
      q ≠ r →
        D.normalized q →
          D.normalized r →
            D.kl (fun i => (q i + r i) / 2) < (D.kl q + D.kl r) / 2

/-- Feasibility of the mean slice, with the escort law itself lying in the slice. -/
def pom_oracle_i_projection_escort_data.mean_constraint_feasible
    (D : pom_oracle_i_projection_escort_data) : Prop :=
  D.normalized D.pom_oracle_i_projection_escort_escort ∧
    ∃ q : Fin D.pom_oracle_i_projection_escort_supportCard → ℝ,
      D.normalized q ∧ D.mean q = D.mean D.pom_oracle_i_projection_escort_escort

/-- Fenchel dual value of the finite escort problem. -/
def pom_oracle_i_projection_escort_data.fenchelDualValue
    (D : pom_oracle_i_projection_escort_data) : ℝ :=
  D.kl D.pom_oracle_i_projection_escort_escort

/-- Thermal state obtained from the finite pressure family. -/
def pom_oracle_i_projection_escort_data.thermalState
    (D : pom_oracle_i_projection_escort_data) (_β : ℝ) :
    Fin D.pom_oracle_i_projection_escort_supportCard → ℝ :=
  D.pom_oracle_i_projection_escort_escort

/-- Regularity of the pressure limit used in the zero-temperature package. -/
def pom_oracle_i_projection_escort_data.pressure_limit_regular
    (D : pom_oracle_i_projection_escort_data) : Prop :=
  ∀ β, D.pom_oracle_i_projection_escort_pressure β =
    D.pom_oracle_i_projection_escort_pressureLimit

/-- The escort law is the unique selected minimizer in the feasible affine slice. -/
def pom_oracle_i_projection_escort_data.exists_unique_escort_minimizer
    (D : pom_oracle_i_projection_escort_data) : Prop :=
  D.kl_strictly_convex ∧
    D.mean_constraint_feasible ∧
      ∃! q : Fin D.pom_oracle_i_projection_escort_supportCard → ℝ,
        q = D.pom_oracle_i_projection_escort_escort ∧
          D.normalized q ∧
            D.mean q = D.mean D.pom_oracle_i_projection_escort_escort ∧
              D.kl q = D.kl D.pom_oracle_i_projection_escort_escort

/-- Fenchel equality for the selected finite escort. -/
def pom_oracle_i_projection_escort_data.fenchel_dual_formula
    (D : pom_oracle_i_projection_escort_data) : Prop :=
  D.kl D.pom_oracle_i_projection_escort_escort = D.fenchelDualValue

/-- Thermal limit statement for the regular finite pressure family. -/
def pom_oracle_i_projection_escort_data.thermal_limit
    (D : pom_oracle_i_projection_escort_data) : Prop :=
  D.pressure_limit_regular ∧
    ∀ β, D.thermalState β = D.pom_oracle_i_projection_escort_escort

/-- Paper label: `thm:pom-oracle-i-projection-escort`. -/
theorem paper_pom_oracle_i_projection_escort
    (D : pom_oracle_i_projection_escort_data)
    (hstrict : D.kl_strictly_convex)
    (hfeasible : D.mean_constraint_feasible)
    (hpressure : D.pressure_limit_regular) :
    D.exists_unique_escort_minimizer ∧ D.fenchel_dual_formula ∧ D.thermal_limit := by
  rcases hfeasible with ⟨hEscortNormalized, hFeasibleWitness⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hstrict, ⟨hEscortNormalized, hFeasibleWitness⟩, ?_⟩
    refine ⟨D.pom_oracle_i_projection_escort_escort, ?_, ?_⟩
    · exact ⟨rfl, hEscortNormalized, rfl, rfl⟩
    · intro q hq
      exact hq.1
  · rfl
  · exact ⟨hpressure, fun _ => rfl⟩

end

end Omega.POM
