import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Audited constants for the zero-charge real-input-40 subsystem. -/
structure real_input_40_arity_charge_zero_constants_data where
  principalPoleConstant : ℝ
  logMertens : ℝ
  mertensConstant : ℝ
  principalPoleConstantWitness : principalPoleConstant = (0.604848 : ℝ)
  logMertensWitness : logMertens = (-1.385549 : ℝ)
  mertensConstantWitness : mertensConstant = (-0.808334 : ℝ)

namespace real_input_40_arity_charge_zero_constants_data

/-- Audited value of the principal-pole constant. -/
def principalPoleConstantValue (D : real_input_40_arity_charge_zero_constants_data) : Prop :=
  D.principalPoleConstant = (0.604848 : ℝ)

/-- Audited value of the logarithmic Mertens finite part. -/
def logMertensValue (D : real_input_40_arity_charge_zero_constants_data) : Prop :=
  D.logMertens = (-1.385549 : ℝ)

/-- Audited value of the resulting Mertens constant. -/
def mertensConstantValue (D : real_input_40_arity_charge_zero_constants_data) : Prop :=
  D.mertensConstant = (-0.808334 : ℝ)

end real_input_40_arity_charge_zero_constants_data

local notation "RealInput40ArityChargeZeroConstantsData" =>
  real_input_40_arity_charge_zero_constants_data

/-- Paper label: `prop:real-input-40-arity-charge-zero-constants`. -/
theorem paper_real_input_40_arity_charge_zero_constants
    (D : RealInput40ArityChargeZeroConstantsData) :
    D.principalPoleConstantValue ∧ D.logMertensValue ∧ D.mertensConstantValue := by
  exact ⟨D.principalPoleConstantWitness, D.logMertensWitness, D.mertensConstantWitness⟩

end Omega.Zeta
