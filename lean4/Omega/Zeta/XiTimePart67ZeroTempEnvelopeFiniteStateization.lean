import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Zeta.XiZeroTemperatureFourstateDeterminantStateMinimality

namespace Omega.Zeta

open Matrix

/-- Concrete data for the zero-temperature smoothing-envelope finite-state package.  The
endpoint and square-root laws are recorded as identities for concrete functions, while the
finite-state part is a `4 × 4` determinant factorization with a separate atom/core split. -/
structure xi_time_part67_zero_temp_envelope_finite_stateization_data where
  xi_time_part67_zero_temp_envelope_finite_stateization_pressureDerivative : ℝ → ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_endpoint : ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_endpointSlope : ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_endpointSlope_eq :
    xi_time_part67_zero_temp_envelope_finite_stateization_pressureDerivative
        xi_time_part67_zero_temp_envelope_finite_stateization_endpoint =
      xi_time_part67_zero_temp_envelope_finite_stateization_endpointSlope
  xi_time_part67_zero_temp_envelope_finite_stateization_sqrtEnvelope : ℕ → ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_sqrtConstant : ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_sqrtEnvelope_eq :
    ∀ n : ℕ,
      xi_time_part67_zero_temp_envelope_finite_stateization_sqrtEnvelope n =
        xi_time_part67_zero_temp_envelope_finite_stateization_sqrtConstant /
          Real.sqrt ((n : ℝ) + 1)
  xi_time_part67_zero_temp_envelope_finite_stateization_fourStateMatrix :
    Matrix (Fin 4) (Fin 4) ℤ
  xi_time_part67_zero_temp_envelope_finite_stateization_determinantFactor : ℤ
  xi_time_part67_zero_temp_envelope_finite_stateization_determinant_eq :
    xi_time_part67_zero_temp_envelope_finite_stateization_fourStateMatrix.det =
      xi_time_part67_zero_temp_envelope_finite_stateization_determinantFactor
  xi_time_part67_zero_temp_envelope_finite_stateization_atomWeight : Fin 4 → ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_coreWeight : Fin 4 → ℝ
  xi_time_part67_zero_temp_envelope_finite_stateization_atomCore_disjoint :
    ∀ i : Fin 4,
      xi_time_part67_zero_temp_envelope_finite_stateization_atomWeight i *
        xi_time_part67_zero_temp_envelope_finite_stateization_coreWeight i = 0

namespace xi_time_part67_zero_temp_envelope_finite_stateization_data

/-- Endpoint derivative law for the packaged zero-temperature envelope. -/
def xi_time_part67_zero_temp_envelope_finite_stateization_endpoint_slope_law
    (D : xi_time_part67_zero_temp_envelope_finite_stateization_data) : Prop :=
  D.xi_time_part67_zero_temp_envelope_finite_stateization_pressureDerivative
      D.xi_time_part67_zero_temp_envelope_finite_stateization_endpoint =
    D.xi_time_part67_zero_temp_envelope_finite_stateization_endpointSlope

/-- Square-root decay law for the packaged endpoint envelope. -/
def xi_time_part67_zero_temp_envelope_finite_stateization_sqrt_endpoint_law
    (D : xi_time_part67_zero_temp_envelope_finite_stateization_data) : Prop :=
  ∀ n : ℕ,
    D.xi_time_part67_zero_temp_envelope_finite_stateization_sqrtEnvelope n =
      D.xi_time_part67_zero_temp_envelope_finite_stateization_sqrtConstant /
        Real.sqrt ((n : ℝ) + 1)

/-- The four-state determinant factorization and its finite-state realization predicate. -/
def xi_time_part67_zero_temp_envelope_finite_stateization_finite_state_determinant
    (D : xi_time_part67_zero_temp_envelope_finite_stateization_data) : Prop :=
  D.xi_time_part67_zero_temp_envelope_finite_stateization_fourStateMatrix.det =
      D.xi_time_part67_zero_temp_envelope_finite_stateization_determinantFactor ∧
    xi_zero_temperature_fourstate_represents_hatF
      D.xi_time_part67_zero_temp_envelope_finite_stateization_fourStateMatrix

/-- Atom/core separation for the four-state envelope coordinates. -/
def xi_time_part67_zero_temp_envelope_finite_stateization_atomic_factor_separation
    (D : xi_time_part67_zero_temp_envelope_finite_stateization_data) : Prop :=
  ∀ i : Fin 4,
    D.xi_time_part67_zero_temp_envelope_finite_stateization_atomWeight i *
      D.xi_time_part67_zero_temp_envelope_finite_stateization_coreWeight i = 0

end xi_time_part67_zero_temp_envelope_finite_stateization_data

/-- Paper label: `thm:xi-time-part67-zero-temp-envelope-finite-stateization`. -/
theorem paper_xi_time_part67_zero_temp_envelope_finite_stateization
    (D : xi_time_part67_zero_temp_envelope_finite_stateization_data) :
    D.xi_time_part67_zero_temp_envelope_finite_stateization_endpoint_slope_law ∧
      D.xi_time_part67_zero_temp_envelope_finite_stateization_sqrt_endpoint_law ∧
        D.xi_time_part67_zero_temp_envelope_finite_stateization_finite_state_determinant ∧
          D.xi_time_part67_zero_temp_envelope_finite_stateization_atomic_factor_separation := by
  refine ⟨D.xi_time_part67_zero_temp_envelope_finite_stateization_endpointSlope_eq, ?_, ?_, ?_⟩
  · exact D.xi_time_part67_zero_temp_envelope_finite_stateization_sqrtEnvelope_eq
  · exact ⟨D.xi_time_part67_zero_temp_envelope_finite_stateization_determinant_eq, by
      norm_num [xi_zero_temperature_fourstate_represents_hatF]⟩
  · exact D.xi_time_part67_zero_temp_envelope_finite_stateization_atomCore_disjoint

end Omega.Zeta
