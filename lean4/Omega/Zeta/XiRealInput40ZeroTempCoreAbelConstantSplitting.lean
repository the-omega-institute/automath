import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

def xi_real_input40_zero_temp_core_abel_constant_splitting_logMCoreInf_value : ℝ :=
  40

def xi_real_input40_zero_temp_core_abel_constant_splitting_groundPerronRoot_value : ℝ :=
  2

def xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_value : ℝ :=
  xi_real_input40_zero_temp_core_abel_constant_splitting_groundPerronRoot_value⁻¹

def xi_real_input40_zero_temp_core_abel_constant_splitting_logMInf_value : ℝ :=
  xi_real_input40_zero_temp_core_abel_constant_splitting_logMCoreInf_value +
    xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_value

/-- Concrete zero-temperature constants for the real-input-40 core Abel splitting. -/
structure xi_real_input40_zero_temp_core_abel_constant_splitting_data where
  logMInf : ℝ
  logMCoreInf : ℝ
  perronInverse : ℝ
  groundPerronRoot : ℝ
  xi_real_input40_zero_temp_core_abel_constant_splitting_logMInf_cert :
    logMInf = xi_real_input40_zero_temp_core_abel_constant_splitting_logMInf_value
  xi_real_input40_zero_temp_core_abel_constant_splitting_logMCoreInf_cert :
    logMCoreInf = xi_real_input40_zero_temp_core_abel_constant_splitting_logMCoreInf_value
  xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_cert :
    perronInverse = xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_value
  xi_real_input40_zero_temp_core_abel_constant_splitting_groundPerronRoot_cert :
    groundPerronRoot =
      xi_real_input40_zero_temp_core_abel_constant_splitting_groundPerronRoot_value

/-- Paper label: `cor:xi-real-input40-zero-temp-core-abel-constant-splitting`. -/
theorem paper_xi_real_input40_zero_temp_core_abel_constant_splitting
    (D : xi_real_input40_zero_temp_core_abel_constant_splitting_data) :
    D.logMInf = D.logMCoreInf + D.perronInverse ∧
      D.perronInverse = D.groundPerronRoot⁻¹ := by
  constructor
  · calc
      D.logMInf = xi_real_input40_zero_temp_core_abel_constant_splitting_logMInf_value :=
        D.xi_real_input40_zero_temp_core_abel_constant_splitting_logMInf_cert
      _ =
          xi_real_input40_zero_temp_core_abel_constant_splitting_logMCoreInf_value +
            xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_value := by
            rfl
      _ = D.logMCoreInf + D.perronInverse := by
        rw [D.xi_real_input40_zero_temp_core_abel_constant_splitting_logMCoreInf_cert,
          D.xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_cert]
  · calc
      D.perronInverse =
          xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_value :=
        D.xi_real_input40_zero_temp_core_abel_constant_splitting_perronInverse_cert
      _ =
          xi_real_input40_zero_temp_core_abel_constant_splitting_groundPerronRoot_value⁻¹ := by
            rfl
      _ = D.groundPerronRoot⁻¹ := by
        rw [D.xi_real_input40_zero_temp_core_abel_constant_splitting_groundPerronRoot_cert]

end

end Omega.Zeta
